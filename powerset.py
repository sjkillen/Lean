def powerset(l: list):
    if len(l) == 0:
        return [[]]
    r = powerset(l[1:])
    return [[l[0], *rr] for rr in r] + r


def powerset(l: list):
    if len(l) == 0:
        return {frozenset(),}
    l = set(l)
    front = l.pop()
    r = powerset(l)
    return {frozenset((front,)) | rr for rr in r} | r


def powerset(l: list):
    match l:
        case tuple():
            return (tuple(),)
        case f, *r:
            return (m := powerset(r)) + [[f, *rr] for rr in m]

