"""Bounded proof-producing word search for ONE fixed relation-module quotient.

No Knuth--Bendix completion, new equations, or negative membership decisions.
The original GAP algorithms are neither imported nor changed here.
"""
import collections
import time


def reduce_word(word):
    result = []
    for x in word:
        if result and result[-1] == -x:
            result.pop()
        else:
            result.append(x)
    return tuple(result)


def inverse(word):
    return tuple(-x for x in reversed(word))


def quotient(rank, prime, relators, candidates):
    """GAP commutator convention [x,R]=x^-1 R^-1 x R. Keep empty rows."""
    output, labels = [], []
    for x in range(1, rank + 1):
        for j, r in enumerate(relators, 1):
            output.append(reduce_word((-x,) + inverse(r) + (x,) + tuple(r)))
            labels.append({"kind": "commutator", "generator": x, "relator": j})
    for j, r in enumerate(relators, 1):
        output.append(reduce_word(tuple(r) * prime))
        labels.append({"kind": "power", "relator": j, "prime": prime})
    for j, s in enumerate(candidates, 1):
        output.append(reduce_word(s))
        labels.append({"kind": "candidate", "candidate": j})
    return output, labels


class FixedQuotient:
    """A finite index of cyclic relator splits, built once for all targets.

    If R^sign=U*V, then U^-1 R^sign U is the cyclic rotation V*U.
    Splitting that rotation as L*T yields the valid rule L -> T^-1.
    Replacing P*L*Q by P*T^-1*Q records the conjugate by P*U^-1.
    All equations remain consequences of the SAME fixed input relators.
    """
    def __init__(self, relations, *, seconds=5, max_rules=10000, max_states=3000):
        if not 0 < seconds <= 5 or not 1 <= max_rules <= 20000 or not 1 <= max_states <= 10000:
            raise ValueError("experimental limits exceed the small-test guard")
        self.deadline = time.monotonic() + seconds
        self.max_states = max_states
        self.options = collections.defaultdict(list)
        self.rule_count = 0
        self.build_limit = False
        self.max_length = 0
        # Short equations first, retaining ORIGINAL relation indices in proofs.
        for offset in sorted(range(len(relations)), key=lambda j: (len(relations[j]), j)):
            i, relation = offset + 1, relations[offset]
            r = reduce_word(relation)
            for sign in (1, -1):
                v = r if sign == 1 else inverse(r)
                for cut in range(len(v)):
                    rot = reduce_word(v[cut:] + v[:cut])
                    # Only this finite set of splits; small expansions permit
                    # simple Bezout examples without claiming completeness.
                    lower = max(1, (len(rot) - 3) // 2)
                    for k in range(lower, len(rot) + 1):
                        if time.monotonic() >= self.deadline or self.rule_count >= max_rules:
                            self.build_limit = True
                            return
                        left, right = rot[:k], inverse(rot[k:])
                        item = (right, i, sign, inverse(v[:cut]))
                        if left == right or item in self.options[left]:
                            continue
                        self.options[left].append(item)
                        self.max_length = max(self.max_length, len(left))
                        self.rule_count += 1

    def prove(self, target):
        start = reduce_word(target)
        queue = collections.deque([(start, [])])
        seen = {start}
        visited = 0
        length_limit = len(start) + 6
        while queue and visited < self.max_states and time.monotonic() < self.deadline:
            word, proof = queue.popleft()
            visited += 1
            if not word:
                return {"status": "certified", "factors": proof, "states": visited}
            for pos in range(len(word)):
                for size in range(min(self.max_length, len(word) - pos), 0, -1):
                    for right, index, sign, conjugator in self.options.get(word[pos:pos + size], ()):
                        result = reduce_word(word[:pos] + right + word[pos + size:])
                        if len(result) > length_limit or result in seen:
                            continue
                        new_proof = proof + [[list(reduce_word(word[:pos] + conjugator)), index, sign]]
                        if not result:
                            return {"status": "certified", "factors": new_proof, "states": visited}
                        seen.add(result)
                        if len(seen) > self.max_states:
                            return {"status": "unresolved", "reason": "state_limit", "states": visited}
                        queue.append((result, new_proof))
        reason = "time_limit" if time.monotonic() >= self.deadline else "state_limit" if queue else "finite_search_exhausted"
        return {"status": "unresolved", "reason": reason, "states": visited}


def produce(problem, **limits):
    relations, labels = quotient(problem["rank"], problem["prime"], problem["relators"], problem["candidates"])
    fixed = FixedQuotient(relations, **limits)
    answers = [fixed.prove(r) for r in problem["relators"]]
    return {"problem": problem, "quotient_relators": [list(r) for r in relations],
            "quotient_labels": labels, "targets": answers,
            "rule_count": fixed.rule_count, "rule_index_builds": 1,
            "rule_build_limit": fixed.build_limit,
            "limits": {"seconds": limits.get("seconds", 5), "max_states": limits.get("max_states", 3000),
                       "max_rules": limits.get("max_rules", 10000), "length_growth": 6},
            "method": "fixed finite cyclic-split search; no completion; unresolved is not nonmembership"}
