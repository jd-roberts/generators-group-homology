"""Bounded experimental shortlex completion. No arithmetic inputs at the CLI.

Proofs are flat products q Q_i^sign q^-1 for lhs rhs^-1. Retain old
rules: new equations are simplified, but old proofs never change meaning.
"""
import heapq
import time
from experiments.relation_span import reduce_word as red, inverse as inv, quotient


class Budget(Exception):
    pass


def invert(proof):
    return [(q, i, -s) for q, i, s in reversed(proof)]


def conjugate(word, proof):
    return [(red(tuple(word) + tuple(q)), i, s) for q, i, s in proof]


def order(word):
    # Fixed alphabet -n < ... < -1 < 1 < ... < n; shortlex is a
    # well-founded, context-compatible monoid order.
    return len(word), tuple(word)


class Completion:
    def __init__(self, rank, relations, *, seconds=1, max_rules=256,
                 max_pairs=4000, max_word=128, max_factors=2000, max_steps=2000):
        if not (0 < seconds <= 5 and 1 <= max_rules <= 1000 and
                1 <= max_pairs <= 20000 and 1 <= max_word <= 1024 and
                1 <= max_factors <= 10000 and 1 <= max_steps <= 10000):
            raise ValueError('experimental budget outside guard')
        if max_rules < 2 * rank:
            raise ValueError('rule budget must fit free cancellation rules')
        self.deadline = time.monotonic() + seconds
        self.limits = dict(seconds=seconds, max_rules=max_rules, max_pairs=max_pairs,
                           max_word=max_word, max_factors=max_factors, max_steps=max_steps)
        self.rules, self.pending, self.queued = [], [], set()
        self.pairs = self.reductions = self.serial = 0
        self.truncated = set()
        self.max_queue = self.max_equation = 0
        self.equations = set()
        self.goal_answers = None
        self.stop_reason = 'pending_exhausted_without_confluence_claim'
        # Free cancellation rules are algebraic identities, requiring no factors.
        for x in range(1, rank + 1):
            for y in (x, -x):
                self.add_rule((y, -y), (), [], 'free')
        try:
            for i, relation in enumerate(relations, 1):
                v = red(relation)
                self.equation(v, (), [((), i, 1)], 'input')
                # One balanced split per rotation/sign, not all possible splits.
                for sign in (1, -1):
                    w = v if sign == 1 else inv(v)
                    for cut in range(len(w)):
                        self.tick()
                        rot = w[cut:] + w[:cut]
                        k = (len(rot) + 1) // 2
                        self.equation(rot[:k], inv(rot[k:]),
                                      [(inv(w[:cut]), i, sign)], 'cyclic_seed')
        except Budget as exc:
            self.truncated.add(str(exc))

    def tick(self):
        if time.monotonic() >= self.deadline:
            raise Budget('time_limit')

    def bound_proof(self, proof):
        if len(proof) > self.limits['max_factors']:
            raise Budget('factor_limit')
        return proof

    def reduce(self, word):
        word, proof = red(word), []
        for _ in range(self.limits['max_steps']):
            self.tick()
            found = False
            # Leftmost, longest lhs first, stable creation order to break ties.
            for pos in range(len(word)):
                choices = [r for r in self.rules if word[pos:pos+len(r['lhs'])] == r['lhs']]
                if not choices:
                    continue
                rule = min(choices, key=lambda r: (-len(r['lhs']), r['id']))
                proof += conjugate(word[:pos], rule['factors'])
                self.bound_proof(proof)
                word = red(word[:pos] + rule['rhs'] + word[pos+len(rule['lhs']):])
                self.reductions += 1
                found = True
                break
            if not found:
                return word, proof
        raise Budget('reduction_step_limit')

    def equation(self, lhs, rhs, proof, origin):
        self.tick()
        lhs, rhs = red(lhs), red(rhs)
        self.max_equation = max(self.max_equation, len(lhs), len(rhs))
        if max(len(lhs), len(rhs)) > self.limits['max_word']:
            self.truncated.add('word_limit')
            return
        left, lp = self.reduce(lhs)
        right, rp = self.reduce(rhs)
        if left == right:
            return
        proof = self.bound_proof(invert(lp) + list(proof) + rp)
        if order(left) < order(right):
            left, right, proof = right, left, invert(proof)
        self.add_rule(left, right, proof, origin)

    def add_rule(self, lhs, rhs, proof, origin):
        key = (lhs, rhs)
        if key in self.equations:
            return
        if len(self.rules) >= self.limits['max_rules']:
            raise Budget('rule_limit')
        self.equations.add(key)
        rule = dict(id=len(self.rules), lhs=lhs, rhs=rhs, factors=proof, origin=origin)
        self.rules.append(rule)
        for previous in self.rules:
            pair = (previous['id'], rule['id'])
            if len(self.queued) >= self.limits['max_pairs']:
                self.truncated.add('pair_limit')
                continue
            if pair not in self.queued:
                self.queued.add(pair)
                # Short consequences/overlaps are favored, with FIFO ties.
                priority = len(previous['lhs']) + len(lhs)
                heapq.heappush(self.pending, (priority, self.serial, pair))
                self.serial += 1
        self.max_queue = max(self.max_queue, len(self.pending))

    def overlaps(self, a, b):
        u, v = a['lhs'], b['lhs']
        # Includes proper overlaps, inclusion ambiguities and both directions.
        for offset in range(1-len(v), len(u)):
            self.tick()
            low, high = min(0, offset), max(len(u), offset+len(v))
            start, stop = max(0, offset), min(len(u), offset+len(v))
            if any(u[j] != v[j-offset] for j in range(start, stop)):
                continue
            common = tuple(u[j] if 0 <= j < len(u) else v[j-offset] for j in range(low, high))
            if len(common) > self.limits['max_word']:
                self.truncated.add('overlap_word_limit')
                continue
            pa, pb = -low, offset-low
            left = common[:pa] + a['rhs'] + common[pa+len(u):]
            right = common[:pb] + b['rhs'] + common[pb+len(v):]
            proof = invert(conjugate(common[:pa], a['factors'])) + conjugate(common[:pb], b['factors'])
            self.equation(left, right, proof, 'critical_pair')

    def complete(self, goals=()):
        try:
            while self.pending:
                self.tick()
                _, _, (i, j) = heapq.heappop(self.pending)
                self.pairs += 1
                before = len(self.rules)
                self.overlaps(self.rules[i], self.rules[j])
                if goals and len(self.rules) != before:
                    answers = [self.prove(word) for word in goals]
                    if all(a['status'] == 'certified' for a in answers):
                        self.goal_answers = answers
                        self.stop_reason = 'targets_certified'
                        return
        except Budget as exc:
            self.truncated.add(str(exc))
            self.stop_reason = str(exc)
        # Never assert confluence/completeness: bounded seeding and proof caps
        # can omit equations, and no independent confluence checker is supplied.

    def prove(self, word):
        try:
            normal, proof = self.reduce(word)
            return dict(status='certified', factors=proof) if not normal else dict(status='unresolved', reason='nonidentity_without_confluence', remainder=normal)
        except Budget as exc:
            return dict(status='unresolved', reason=str(exc))


def produce(problem, **limits):
    start = time.monotonic()
    relations, labels = quotient(problem['rank'], problem['prime'], problem['relators'], problem['candidates'])
    engine = Completion(problem['rank'], relations, **limits)
    # Save cheap successes before spending the shared budget on completion.
    initial = [engine.prove(r) for r in problem['relators']]
    if all(a['status'] == 'certified' for a in initial):
        engine.stop_reason = 'targets_certified_before_completion'
    else:
        engine.complete(problem['relators'])
    targets = engine.goal_answers or [a if a['status'] == 'certified' else engine.prove(r) for a, r in zip(initial, problem['relators'])]
    return dict(problem=problem, quotient_relators=relations, quotient_labels=labels,
                targets=targets, rules=engine.rules, limits=engine.limits,
                metrics=dict(search_wall_seconds=time.monotonic()-start, rule_count=len(engine.rules),
                             critical_pairs=engine.pairs, reduction_steps=engine.reductions,
                             max_pending_pairs=engine.max_queue, max_equation_length=engine.max_equation,
                             truncations=sorted(engine.truncated), stop_reason=engine.stop_reason,
                             initially_certified=sum(a['status']=='certified' for a in initial)),
                method='bounded proof-producing shortlex critical-pair completion; no confluence assertion')
