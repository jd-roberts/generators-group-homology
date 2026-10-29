#!/usr/bin/env python3
"""Known-trace coverage certificates and static job selection. No goal search."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from experiments.relation_span import reduce_word as red,inverse as inv


def reduce_with_certificate(word,rules):
    w=red(word);proof=[]
    for step in range(2000):
        found=False
        for pos in range(len(w)):
            matches=[r for r in rules if w[pos:pos+len(r['lhs'])]==tuple(r['lhs'])]
            if not matches:continue
            rule=min(matches,key=lambda r:(-len(r['lhs']),r['id']))
            proof.append([list(w[:pos]),rule['id']+1,1])
            if len(proof)>2000:raise ValueError('reverse certificate factor limit')
            w=red(w[:pos]+tuple(rule['rhs'])+w[pos+len(rule['lhs']):]);found=True;break
        if not found:return w,proof
    raise ValueError('reverse certificate step limit')


def compatible(u,v):
    # Static substring/boundary matching ONLY: do not form critical equations.
    u=''.join(chr(x+7) for x in u);v=''.join(chr(x+7) for x in v)
    if u in v or v in u:return True
    return any(u[-k:]==v[:k] or v[-k:]==u[:k] for k in range(1,min(len(u),len(v))))


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args();b=a.output;b.mkdir(parents=True,exist_ok=False)
    prior=ROOT/'benchmarks/results/prime7-a4-1-2026-10-28'
    trace=(prior/'worker/stdout.txt').read_bytes();events=[json.loads(l) for l in trace.splitlines()]
    rules=[e['rule'] for e in events if e['kind']=='rule'];assert len(rules)==233
    raw=(prior/'input.json.gz').read_bytes();source=json.loads(gzip.decompress(raw));q=source['quotient_relators'];assert len(q)==236
    combined=rules+[dict(id=233+i,lhs=q[216+i],rhs=[],factors=[[[],217+i,1]],origin='unsimplified_Q'+str(217+i)) for i in range(8)]
    oldplan=json.loads((prior/'preparation/plan.json').read_text());seeded=events[-1]['original_rows_seeded'];assert seeded==oldplan['completion_input_order'][:228]
    prefix=next(r['id'] for r in rules if r['origin'].startswith('original_Q_'));assert prefix==42
    coverage={}
    for i in seeded:
        new=rules[prefix] if prefix<len(rules) and rules[prefix]['origin']=='original_Q_'+str(i) else None
        w,proof=reduce_with_certificate(q[i-1],rules[:prefix])
        if new:
            assert w==tuple(new['lhs']) and new['rhs']==[]
            proof.append([[],new['id']+1,1]);prefix+=1
        else:assert not w,('uncovered original row',i,w)
        coverage[str(i)]=proof
    assert prefix==233
    for i in range(217,225):coverage[str(i)]=[[[],233+(i-217)+1,1]]
    assert len(coverage)==236
    # 64 distinct matched partners per new row, or all if fewer. Checkpoint
    # partners only avoid duplicates across long-power pools. Self jobs excluded.
    pools=[]
    for long_id in range(233,241):
        partners=[r for r in rules if compatible(r['lhs'],combined[long_id]['lhs'])]
        partners.sort(key=lambda r:(r['origin']=='free',len(r['lhs']),-sum(abs(x)==5 for x in r['lhs']),r['id']))
        pools.append([[r['id'],long_id] for r in partners[:64]])
    assert all(pools),'every long power must have compatible partners'
    core=[]
    for i,r in enumerate(rules):
        for s in rules[i:]:
            if compatible(r['lhs'],s['lhs']):core.append([i,s['id']])
    core.sort(key=lambda pair:(not all(any(abs(x)==5 for x in rules[k]['lhs']) for k in pair),sum(len(rules[k]['lhs']) for k in pair),pair[1],pair[0]))
    long_jobs=[]
    for k in range(max(map(len,pools))):
        for pool in pools:
            if k<len(pool):long_jobs.append(pool[k])
    # One job per new row first; then alternate core and remaining long jobs.
    initial=long_jobs[:8];tail=long_jobs[8:];jobs=initial[:];ci=li=0
    while len(jobs)<4000 and (ci<len(core) or li<len(tail)):
        if ci<len(core):jobs.append(core[ci]);ci+=1
        if len(jobs)<4000 and li<len(tail):jobs.append(tail[li]);li+=1
    assert len(jobs)==4000 and len(set(map(tuple,jobs)))==4000
    counts={str(i):sum(i in pair for pair in jobs) for i in range(233,241)}
    for i in range(8):assert jobs[i][1]==233+i
    checkpoint=dict(rules=combined,original_Q_coverage=coverage,prior_trace_sha256=hashlib.sha256(trace).hexdigest())
    plan=dict(only_target=7,target_word=[5]*4,jobs=jobs,long_power_job_counts=counts,
              selection='first one nonfree-preferred shortest matching checkpoint partner per long row; then interleave target-letter/short core pairs with round-robin long pools (up to 64 per row); fill remaining from core',
              newly_derived_rule_jobs='none: all 4000 cumulative jobs frozen before search; new rules can simplify remaining jobs',
              limits=dict(search_seconds=5,memory_bytes=536870912,cpu_seconds=6,wall_seconds=10,output_bytes=8388608,max_rules=256,max_jobs=4000,max_word=512,max_factors=2000,max_steps=2000),
              preparation_scope='known input coverage replay and static left-side matching only, no target or critical-equation search')
    (b/'checkpoint.json').write_text(json.dumps(checkpoint,separators=(',',':'))+'\n')
    (b/'schedule.json').write_text(json.dumps(plan,indent=2)+'\n');(b/'prior-trace.jsonl').write_bytes(trace);(b/'input.json.gz').write_bytes(raw)
    print(json.dumps(dict(checkpoint_rules=241,reverse_input_certificates=236,jobs=len(jobs),long_power_jobs=counts,first_eight=jobs[:8]),indent=2))


if __name__=='__main__':main()
