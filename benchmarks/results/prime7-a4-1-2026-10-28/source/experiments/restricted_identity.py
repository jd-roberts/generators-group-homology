"""Checked indexing adapter; no search or arithmetic identities are computed."""
from experiments.relation_span import reduce_word


def subset(base, indices):
    if len(set(indices))!=len(indices) or any(type(i) is not int or not 1<=i<=len(base) for i in indices):
        raise ValueError('invalid original relation indices')
    return [list(reduce_word(base[i-1])) for i in indices]


def map_factors(proof, indices):
    output=[]
    for q,i,sign in proof:
        if type(i) is not int or not 1<=i<=len(indices) or sign not in (-1,1):
            raise ValueError('invalid local proof index')
        output.append([list(q),indices[i-1],sign])
    return output


def map_record(record, indices):
    rules=[]
    for rule in record['rules']:
        rules.append(dict(rule, factors=map_factors(rule['factors'],indices)))
    targets=[dict(a,factors=map_factors(a['factors'],indices)) if a['status']=='certified' else a for a in record['targets']]
    return dict(record,rules=rules,targets=targets)
