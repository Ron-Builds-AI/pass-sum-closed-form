# One-off: the vanishing pairs at weights (1, 4, 2) and (1, 9, 2) on p -300..1, l 0..3000, from the residue's definition
# (exact integers), against the groups F-056 quotes. Prints the zero list; writes nothing.
from math import comb
def Q(p, l, c):
    n = l + p
    return sum(c[m] * (-1) ** (l + p - m) * (comb(l, m - p) if 0 <= m - p <= l else 0) for m in range(3) if m <= n)
for c in ((1, 4, 2), (1, 9, 2), (1, 4, 1)):
    z = [(p, l) for p in range(1, -301, -1) for l in range(max(0, -p), 3001) if Q(p, l, c) == 0]
    print(c, len(z), sorted(z, key=lambda t: (t[1], -t[0]))[:12])
