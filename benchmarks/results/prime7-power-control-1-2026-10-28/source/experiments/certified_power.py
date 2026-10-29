"""Bounded power/conjugation identities, not a general completion algorithm.

Every retained equation is w=1 with a flat product in the ORIGINAL input base.
Only literal free identities, common-root Bezout and inversion+centrality are
used. In particular powers of two different words are never collected.
"""
import time
from experiments.relation_span import reduce_word as red, inverse as inv, quotient


class Limit(Exception):
    pass


def invert(proof):
    return [(q, i, -s) for q, i, s in reversed(proof)]


def conjugate(q, proof):
    return [(red(tuple(q)+tuple(c)), i, s) for c, i, s in proof]


def bezout(a, b):
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r-q*r
        old_s, s = s, old_s-q*s
        old_t, t = t, old_t-q*t
    return old_r, old_s, old_t


def cyclic(word):
    w, prefix = red(word), []
    while len(w) >= 2 and w[0] == -w[-1]:
        prefix.append(w[0])
        w = w[1:-1]
    return tuple(prefix), w


def power_form(word):
    """Exact free equality word=q*root^exponent*q^-1; canonical cyclic root."""
    q, c = cyclic(word)
    if not c:
        return (), 0, ()
    size = next(k for k in range(1,len(c)+1) if len(c)%k == 0 and c == c[:k]*(len(c)//k))
    d, exponent = c[:size], len(c)//size
    choices = []
    for sign, base in ((1,d),(-1,inv(d))):
        for cut in range(size):
            choices.append((base[cut:]+base[:cut], sign*exponent, red(q+base[:cut])))
    root, e, conjugator = min(choices, key=lambda t: (t[0], t[1], t[2]))
    # Defensive internal equality, not a replacement for independent replay.
    expanded = root*e if e >= 0 else inv(root)*(-e)
    if red(conjugator+expanded+inv(conjugator)) != red(word):
        raise ValueError('power normalization identity failed')
    return root, e, conjugator


class PowerSimplifier:
    def __init__(self, relations, *, seconds=1, max_rules=128, max_word=128,
                 max_factors=2000, max_steps=2000):
        if not (0 < seconds <= 1 and 1 <= max_rules <= 128 and
                1 <= max_word <= 128 and 1 <= max_factors <= 2000 and 1 <= max_steps <= 2000):
            raise ValueError('outside bounded experimental limits')
        self.deadline = time.monotonic()+seconds
        self.limits = dict(seconds=seconds,max_rules=max_rules,max_word=max_word,
                           max_factors=max_factors,max_steps=max_steps)
        self.rules, self.powers, self.keys = [], {}, set()
        self.inversions, self.centralities = [], []
        self.truncations, self.operations = set(), 0
        try:
            for i, word in enumerate(relations,1):
                self.add_power(red(word), [((),i,1)], 'input_power_normalization')
                self.patterns(word, [((),i,1)])
            for u,h,sp in self.inversions:
                for v,g,kp in self.centralities:
                    self.tick()
                    if g != h or len(v)%len(u):
                        continue
                    k = len(v)//len(u)
                    if v == inv(u)*k:
                        # [h,u^k] = u^-k * [h,u^-k]^-1 * u^k.
                        kp = conjugate(inv(u)*k, invert(kp))
                    elif v != u*k:
                        continue
                    proof = conjugate(h+u*k, invert(kp))
                    for j in range(1,k+1):
                        self.tick()
                        proof += conjugate(inv(u)*j, sp)
                        self.proof_limit(proof)
                    self.add_power(u*(2*k), proof, 'inversion_and_centrality')
        except Limit as error:
            self.truncations.add(str(error))

    def tick(self):
        self.operations += 1
        if time.monotonic() >= self.deadline:
            raise Limit('time_limit')
        if self.operations > self.limits['max_steps']:
            raise Limit('operation_limit')

    def proof_limit(self, proof):
        if len(proof) > self.limits['max_factors']:
            raise Limit('factor_limit')
        return proof

    def multiple(self, proof, coefficient):
        self.tick()
        if len(proof)*abs(coefficient) > self.limits['max_factors']:
            raise Limit('factor_limit')
        return (proof if coefficient >= 0 else invert(proof))*abs(coefficient)

    def retain(self, word, proof, origin):
        self.tick()
        word = red(word)
        if not word or word in self.keys:
            return
        if len(word) > self.limits['max_word']:
            raise Limit('word_limit')
        self.proof_limit(proof)
        if len(self.rules) >= self.limits['max_rules']:
            raise Limit('rule_limit')
        self.rules.append(dict(id=len(self.rules),lhs=word,rhs=(),factors=proof,origin=origin))
        self.keys.add(word)

    def add_power(self, word, proof, origin):
        self.tick()
        if len(word) > self.limits['max_word']:
            raise Limit('word_limit')
        root, exponent, q = power_form(word)
        if not exponent:
            return
        pp = conjugate(inv(q), proof)
        if exponent < 0:
            exponent, pp = -exponent, invert(pp)
        self.retain(root*exponent, pp, origin)
        previous = self.powers.get(root)
        if previous is None:
            self.powers[root] = (exponent, pp)
            return
        n, old = previous
        d, a, b = bezout(n, exponent)
        if d == n:
            return
        combined = self.proof_limit(self.multiple(old,a)+self.multiple(pp,b))
        self.retain(root*d, combined, 'common_root_bezout')
        self.powers[root] = (d, combined)

    def patterns(self, word, proof):
        q, c = cyclic(word)
        for sign, base in ((1,c),(-1,inv(c))):
            for cut in range(len(base)):
                self.tick()
                r = base[cut:]+base[:cut]
                if len(r) < 4 or len(r)%2:
                    continue
                p = conjugate(inv(red(q+base[:cut])), proof if sign == 1 else invert(proof))
                length = (len(r)-2)//2
                u, h = r[:length], (r[length],)
                if r[length+1:-1] == u and r[-1] == -h[0] and red(u) == u and cyclic(u)[1] == u:
                    self.inversions.append((u,h,p))
                # K=h^-1 v^-1 h v, with a one-letter h; no inference from
                # abelian exponent sums or from centrality of unrelated words.
                h, v = (-r[0],), r[length+2:]
                if r[1:length+1] == inv(v) and r[length+1] == h[0] and cyclic(v)[1] == v:
                    self.centralities.append((v,h,p))

    def prove(self, word):
        try:
            self.tick()
            root, exponent, q = power_form(word)
            if not exponent:
                return dict(status='certified',factors=[])
            power = self.powers.get(root)
            if power is None or exponent%power[0]:
                return dict(status='unresolved',reason='no_applicable_certified_power')
            proof = self.multiple(power[1], exponent//power[0])
            return dict(status='certified', factors=self.proof_limit(conjugate(q,proof)))
        except Limit as error:
            return dict(status='unresolved',reason=str(error))


def produce(problem, **limits):
    started = time.monotonic()
    relations, labels = quotient(problem['rank'],problem['prime'],problem['relators'],problem['candidates'])
    engine = PowerSimplifier(relations,**limits)
    targets = [engine.prove(r) for r in problem['relators']]
    return dict(problem=problem,quotient_relators=relations,quotient_labels=labels,
                targets=targets,rules=engine.rules,limits=engine.limits,
                metrics=dict(search_wall_seconds=time.monotonic()-started,rule_count=len(engine.rules),
                             operations=engine.operations,truncations=sorted(engine.truncations),
                             inversion_patterns=len(engine.inversions),centrality_patterns=len(engine.centralities)),
                method='certified common-root powers and inversion/centrality identities; incomplete')
