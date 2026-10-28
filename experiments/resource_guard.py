#!/usr/bin/env python3
"""Linux OS resource supervisor. One dedicated supervisor owns one process tree."""
import argparse
import ctypes
import errno
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time


def process_table():
    rows = {}
    for path in Path('/proc').glob('[0-9]*/stat'):
        try:
            fields = path.read_text().rsplit(')', 1)[1].split()
            rows[int(path.parent.name)] = {'ppid':int(fields[1]), 'start_ticks':int(fields[19]),
                'rss_kib':int(fields[21])*os.sysconf('SC_PAGE_SIZE')//1024,
                'vsize_bytes':int(fields[20])}
        except (OSError, ValueError, IndexError):
            pass
    return rows


def descendants(table, root):
    found = set()
    frontier = {root}
    while frontier:
        new = {pid for pid, r in table.items() if r['ppid'] in frontier and pid not in found}
        found |= new
        frontier = new
    return found


def kill(pid):
    try:
        os.kill(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def usage_record(usage):
    return {'user_seconds':usage.ru_utime,'system_seconds':usage.ru_stime,'max_rss_kib':usage.ru_maxrss}


def cleanup_tree(worker_pid, observations):
    try:
        os.killpg(worker_pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    reaped=[]
    started=time.monotonic()
    while True:
        table=process_table()
        for pid in descendants(table,os.getpid()):
            observations[(pid,table[pid]['start_ticks'])]={'pid':pid,**table[pid]}
            kill(pid)
        no_children=False
        while True:
            try:
                pid,status,usage=os.wait4(-1,os.WNOHANG)
            except ChildProcessError:
                no_children=True
                break
            if not pid:
                break
            reaped.append({'pid':pid,'returncode':os.waitstatus_to_exitcode(status),**usage_record(usage)})
        if no_children and not descendants(process_table(),os.getpid()):
            return reaped
        if time.monotonic()-started>2:
            raise RuntimeError('descendant cleanup/reaping did not finish')
        time.sleep(.01)


def supervise(command, directory, limits):
    directory=Path(directory)
    directory.mkdir(parents=True,exist_ok=False)
    if ctypes.CDLL(None,use_errno=True).prctl(36,1,0,0,0)!=0:
        raise OSError(ctypes.get_errno(),'PR_SET_CHILD_SUBREAPER failed')
    started=time.monotonic()
    child_command=[sys.executable,str(Path(__file__).resolve()),'--bootstrap',
                   json.dumps(limits,separators=(',',':')),'--',*command]
    observations={}
    peak_rss=0
    wall_killed=False
    interrupted=None
    main_record=None
    failure=None
    with (directory/'stdout.txt').open('wb') as stdout,(directory/'stderr.txt').open('wb') as stderr:
        child=subprocess.Popen(child_command,stdout=stdout,stderr=stderr,start_new_session=True)
        active=True
        def stop(signum,frame):
            nonlocal interrupted
            interrupted=signum
            if active:
                kill(child.pid)
                try:
                    os.killpg(child.pid,signal.SIGKILL)
                except ProcessLookupError:
                    pass
        old_handlers={sig:signal.signal(sig,stop) for sig in (signal.SIGINT,signal.SIGTERM)}
        try:
            while True:
                table=process_table()
                owned=descendants(table,os.getpid())
                peak_rss=max(peak_rss,sum(table[p]['rss_kib'] for p in owned))
                for pid in owned:
                    observations[(pid,table[pid]['start_ticks'])]={'pid':pid,**table[pid]}
                pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                if pid:
                    main_record={'pid':pid,'returncode':os.waitstatus_to_exitcode(status),**usage_record(usage)}
                    break
                if time.monotonic()-started>=limits['wall_seconds']:
                    wall_killed=True
                    kill(child.pid)
                    try:
                        os.killpg(child.pid,signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                if time.monotonic()-started>limits['wall_seconds']+2:
                    raise RuntimeError('worker failed to terminate after SIGKILL')
                time.sleep(.01)
        except BaseException as error:
            failure=repr(error)
        finally:
            active=False
            try:
                reaped=cleanup_tree(child.pid,observations)
            finally:
                for sig,handler in old_handlers.items():
                    signal.signal(sig,handler)
            if main_record is None:
                main_record=next((r for r in reaped if r['pid']==child.pid),None)
            child.returncode=main_record['returncode'] if main_record else 125
    adopted=[r for r in reaped if r['pid']!=child.pid]
    if main_record is None:
        raise RuntimeError('worker reap record missing')
    reason='supervisor_signal' if interrupted else 'wall_limit' if wall_killed else 'completed' if child.returncode==0 else 'process_error'
    if not interrupted and not wall_killed and child.returncode==-signal.SIGXFSZ:
        reason='output_limit'
    cpu=main_record['user_seconds']+main_record['system_seconds']
    if not interrupted and not wall_killed and child.returncode==-signal.SIGKILL and cpu>=limits['cpu_seconds']-.15:
        reason='cpu_limit'
    record={'command':command,'limits':limits,'termination':reason,'returncode':child.returncode,
            'supervisor_signal':interrupted,'supervisor_error':failure,
            'wall_seconds':round(time.monotonic()-started,6),'worker':main_record,
            'sampled_peak_tree_rss_kib':peak_rss,'adopted_children':adopted,
            'observed_processes':list(observations.values()),'cleanup_verified':True,
            'stdout_bytes':(directory/'stdout.txt').stat().st_size,
            'stderr_bytes':(directory/'stderr.txt').stat().st_size,
            'notes':'RLIMIT_AS/CPU/FSIZE are per-process inherited hard limits; wall limit covers the tree. wait4 RSS is a max; sampled RSS sums can double-count shared pages. Supervisor cleanup may add a short tail after worker termination.'}
    (directory/'resources.json').write_text(json.dumps(record,indent=2)+'\n')
    if failure:
        raise RuntimeError(failure)
    return record


def bootstrap(limits, command):
    # Hard=soft: descendants cannot raise these limits after fork/exec.
    resource.setrlimit(resource.RLIMIT_AS, (limits['memory_bytes'],)*2)
    resource.setrlimit(resource.RLIMIT_CPU, (limits['cpu_seconds'],)*2)
    resource.setrlimit(resource.RLIMIT_FSIZE, (limits['output_bytes'],)*2)
    resource.setrlimit(resource.RLIMIT_CORE, (0,0))
    signal.signal(signal.SIGXFSZ, signal.SIG_DFL)
    # If the supervisor itself dies, the direct worker must not survive it.
    parent = os.getppid()
    if ctypes.CDLL(None, use_errno=True).prctl(1, signal.SIGKILL, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), 'PR_SET_PDEATHSIG failed')
    if os.getppid() != parent:
        os._exit(125)
    os.execvpe(command[0], command, os.environ)


def main():
    if len(sys.argv)>1 and sys.argv[1]=='--bootstrap':
        bootstrap(json.loads(sys.argv[2]), sys.argv[4:])
        return
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--memory-mib',type=int,default=512)
    parser.add_argument('--cpu-seconds',type=int,default=6)
    parser.add_argument('--wall-seconds',type=float,default=10)
    parser.add_argument('--output-bytes',type=int,default=8*1024*1024)
    parser.add_argument('command',nargs=argparse.REMAINDER)
    a=parser.parse_args()
    command=a.command[1:] if a.command and a.command[0]=='--' else a.command
    if not command or min(a.memory_mib,a.cpu_seconds,a.wall_seconds,a.output_bytes)<=0:
        parser.error('positive limits and a command are required')
    result=supervise(command,a.output,{'memory_bytes':a.memory_mib*1024*1024,
        'cpu_seconds':a.cpu_seconds,'wall_seconds':a.wall_seconds,'output_bytes':a.output_bytes})
    print(json.dumps({'termination':result['termination'],'returncode':result['returncode'],'cleanup_verified':True}))


if __name__=='__main__':
    main()
