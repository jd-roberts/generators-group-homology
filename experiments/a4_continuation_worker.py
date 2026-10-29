#!/usr/bin/env python3
"""One frozen 241-rule continuation; sole goal a^4; five shared seconds."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sys
import time

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from experiments.checkpoint_completion import CheckpointCompletion


class SharedDeadline(Exception):pass


def emit(event):
    # Avoid a half-emitted job counter record when the five-second alarm fires.
    old=signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGALRM})
    try:
        raw=(json.dumps(event,separators=(',',':'))+'\n').encode()
        while raw:
            count=os.write(1,raw);raw=raw[count:]
    finally:signal.pthread_sigmask(signal.SIG_SETMASK,old)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True);a=p.parse_args();prep=a.base/'preparation'
    checkpoint=json.loads((prep/'checkpoint.json').read_text());plan=json.loads((prep/'schedule.json').read_text())
    assert len(checkpoint['rules'])==241 and len(plan['jobs'])==4000 and plan['only_target']==7
    effective={n:list(resource.getrlimit(getattr(resource,n))) for n in ['RLIMIT_AS','RLIMIT_CPU','RLIMIT_FSIZE']}
    assert effective=={'RLIMIT_AS':[536870912]*2,'RLIMIT_CPU':[6]*2,'RLIMIT_FSIZE':[8388608]*2}
    emit(dict(kind='header',only_target=7,target_word=[5]*4,loaded_rules=241,queued_jobs=4000,effective_os_limits=effective,
              checkpoint_sha256=hashlib.sha256((prep/'checkpoint.json').read_bytes()).hexdigest(),
              schedule_sha256=hashlib.sha256((prep/'schedule.json').read_bytes()).hexdigest()))
    def alarm(sig,frame):raise SharedDeadline()
    previous=signal.signal(signal.SIGALRM,alarm);started=time.monotonic();deadline=started+5;engine=None
    answer=dict(status='unresolved',reason='no_successful_certificate');stop=''
    signal.setitimer(signal.ITIMER_REAL,5)
    try:
        engine=CheckpointCompletion.__new__(CheckpointCompletion)
        engine.__init__(checkpoint['rules'],plan['jobs'],seconds=5,emit=emit);engine.deadline=deadline
        initial=engine.prove((5,5,5,5))
        if initial['status']=='certified':answer=initial;stop='checkpoint_certified'
        else:
            engine.complete([(5,5,5,5)])
            answer=engine.goal_answers[0] if engine.goal_answers else engine.prove((5,5,5,5))
            stop='target_certified' if answer['status']=='certified' else engine.stop_reason
    except SharedDeadline:
        stop='shared_search_time_limit'
        if answer['status']!='certified':answer=dict(status='unresolved',reason=stop)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,previous)
    emit(dict(kind='target',only_target=7,answer=answer))
    emit(dict(kind='summary',only_target=7,search_wall_seconds=time.monotonic()-started,stop_reason=stop,
              rules=len(getattr(engine,'rules',[])),jobs_completed=getattr(engine,'jobs_completed',0),
              accounting=engine.accounting() if engine and hasattr(engine,'pairs') else {},
              reductions=getattr(engine,'reductions',0),max_equation_length=getattr(engine,'max_equation',0),
              truncations=sorted(getattr(engine,'truncated',set()))))


if __name__=='__main__':main()
