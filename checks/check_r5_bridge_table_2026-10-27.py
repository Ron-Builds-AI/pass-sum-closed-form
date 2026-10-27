# One-off: the bridge table of Section 4.6 at k = 4, exact integers, from the definition of Q_n (weights 1, 4, 1). Prints rows; writes nothing.
from math import comb, isqrt
def Q(p, l):
    return sum((1, 4, 1)[m] * (-1) ** (l + p - m) * (comb(l, m - p) if 0 <= m - p <= l else 0) for m in range(3) if m <= l + p)
rows = [(1, 4), (-3, 23), (-18, 94), (-74, 359), (-283, 1348)]
ok = True
for p, l in rows:
    U, V = 5 - 2 * p, 2 * (l + p) + 1
    yU, yV = isqrt(3 * U * U - 2), isqrt(3 * V * V - 2)
    good = Q(p, l) == 0 and yU * yU - 3 * U * U == -2 and yV * yV - 3 * V * V == -2 and U * U - 4 * U * V + V * V == -2 and yU == V - 2 * U and yV == 2 * V - U
    ok &= good
    print(p, l, U, V, yU, yV, U * U - 4 * U * V + V * V, "ok" if good else "BAD")
print("265 held by:", [(p, l) for p, l in rows if 265 in (isqrt(3 * (5 - 2 * p) ** 2 - 2), isqrt(3 * (2 * (l + p) + 1) ** 2 - 2))])
print("ALL PASS" if ok else "FAIL")
