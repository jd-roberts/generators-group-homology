"""Deliberately exceed a specified OS limit; never used for research search."""
import json
import os
from pathlib import Path
import resource
import signal
import sys
import time


def start_ticks(pid):
    return int(Path(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()[19])


def sleeper(pidfile):
    read,write=os.pipe()
    pid=os.fork()
    if pid==0:
        os.close(read)
        os.setsid()  # Deliberately escape the worker's process group.
        os.write(write,b'1');os.close(write)
        time.sleep(60)
        os._exit(0)
    os.close(write)
    assert os.read(read,1)==b'1';os.close(read)
    Path(pidfile).write_text(json.dumps({'parent':{'pid':os.getpid(),'start':start_ticks(os.getpid())},
                                       'child':{'pid':pid,'start':start_ticks(pid)}}))


mode=sys.argv[1]
if mode=='limits':
    print(json.dumps({name:list(resource.getrlimit(getattr(resource,name))) for name in ['RLIMIT_AS','RLIMIT_CPU','RLIMIT_FSIZE']}),flush=True)
else:
    sleeper(sys.argv[2])
    if mode=='memory':
        chunks=[]
        try:
            while True: chunks.append(bytearray(8*1024*1024))
        except MemoryError:
            os.write(2,b'EXPECTED_MEMORY_ERROR\n')
            os._exit(73)
    elif mode=='cpu':
        n=0
        while True: n=(n+1)%1000003
    elif mode=='wall':
        time.sleep(60)
    elif mode=='output':
        signal.signal(signal.SIGXFSZ,signal.SIG_DFL)
        while True: os.write(1,b'x'*65536)
    elif mode=='normal_child':
        os._exit(0)
    elif mode=='crash_child':
        os._exit(17)
    else:
        raise ValueError(mode)
