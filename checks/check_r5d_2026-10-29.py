# Checks for the r5d proof-pieces note (2026-10-29): the r5c checker (check_r5c_2026-10-29.py) with three checks added, A18 for the
# descent at (1,4,2) in the remark on general weights, A19 for the zero off the orbit of (0,0) at (1,9,2), and B3 for Claim 3.1 as
# written out in Section 1.3. The r5c checker is the r5b
# checker (check_r5b_2026-10-27.py, itself the r5 checker with A11 added for r5b's Archimedes paragraph) with A17 added for r5c's
# rewritten remark on general weights (the two Vieta jumps, the chains at (1,4,2) and (1,9,2)), and the figure data looked up in
# paper/fig_r5 (the repository's layout) before fig_r5 beside the checks folder (the r5 build folder's layout, the only one the r5b
# checker looked in).
# Exact arithmetic (Fraction) in part A; mpmath at 40 digits in part B.
# Prints PASS or FAIL per check and ALL PASS at the end; writes CHECK_r5d_2026-10-29.txt beside this file.
import os, sys, time
from fractions import Fraction as Fr
from math import comb, factorial, isqrt
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "CHECK_r5d_2026-10-29.txt")
FIG = next((d for d in (os.path.join(os.path.dirname(HERE), "paper", "fig_r5"), os.path.join(os.path.dirname(HERE), "fig_r5"))
            if os.path.isdir(d)), os.path.join(os.path.dirname(HERE), "paper", "fig_r5"))
C = (1, 4, 1)
lines, fails = [], []
t0 = time.time()

def rep(ok, name, detail=""):
    s = ("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else "")
    print(s); lines.append(s)
    if not ok: fails.append(name)

def binl(l, j):                       # binom(l, j) with 0 outside 0..l
    return comb(l, j) if 0 <= j <= l else 0

def harm(j):
    return sum((Fr(1, i) for i in range(1, j + 1)), Fr(0))

# dual numbers: binom(z, j) and its z-derivative at an integer z, from the product definition
def gbinom_dual(z, j):
    val, der = Fr(1), Fr(0)
    for i in range(j):
        f = Fr(z - i)
        der = der * f + val
        val = val * f
    return val / factorial(j), der / factorial(j)

def Q_dual(n, s, c=C):                # Q_n(s) and Q_n'(s) at integer s, from the definition
    v = d = Fr(0)
    for m in range(0, min(2, n) + 1):
        a, b = gbinom_dual(s + n - m - 1, n - m)
        v += c[m] * a; d += c[m] * b
    return v, d

def Q_closed(p, l):
    n = l + p
    return sum((C[m] * (-1) ** (l + p - m) * binl(l, m - p) for m in range(max(0, p), 3)), 0)

def Qd_closed(p, l):
    s1 = sum((Fr(C[m] * (-1) ** l * factorial(p - m - 1) * factorial(l), factorial(l + p - m))
              for m in range(0, min(2, p - 1) + 1)), Fr(0))
    s2 = sum((C[m] * (-1) ** (l + p - m) * binl(l, m - p) * (harm(l) - harm(m - p))
              for m in range(max(0, p), 3) if m - p <= l), Fr(0))
    return s1 - s2

# ---------------- A. exact ----------------
bad, cnt = [], 0
for p in range(-8, 3):
    for l in range(max(0, -p), 81):
        v, d = Q_dual(l + p, -l)
        cnt += 1
        if v != Q_closed(p, l) or d != Qd_closed(p, l):
            bad.append((p, l))
rep(not bad, "A1 closed forms of Q_n(-l) and Q_n'(-l) against dual numbers from the definition (p -8..2, l max(0,-p)..80)",
    f"{cnt} pairs, mismatches {len(bad)} {bad[:5]}")

ok = True
for l in range(0, 81):
    R = comb(l + 2, 2)
    ok &= Q_closed(2, l) == (-1) ** l
    ok &= Q_closed(1, l) == (-1) ** l * (4 - l)
    ok &= 2 * Q_closed(0, l) == (-1) ** l * (l * l - 9 * l + 2)
    ok &= (-1) ** l * R * Q_closed(2, l) == R                                   # G_l L at p = 2
    ok &= (-1) ** l * R * Q_closed(1, l) == R * (4 - l)                         # G_l L at p = 1
    if l >= 1:
        ok &= Qd_closed(1, l) == (-1) ** l * (Fr(1, l + 1) - 4 * harm(l) + l * (harm(l) - 1))
ok &= Qd_closed(1, 0) == 1 and Q_dual(1, 0)[1] == 1
rep(ok, "A2 the p = 0, 1, 2 lines: Q_{l+p}(-l), G_l L = R_l Q, Q'_{l+1}(-l) for l >= 1 and Q_1'(0) = 1 (l 0..80)")

# F_l = A + B/L exactly, for rational xi: g_j = 1/(xi^(p-j) - 1) is rational
def F_parts(p, l, xi):
    n = l + p
    R = Fr((-1) ** l * comb(l + 2, 2))
    Q = Fr(Q_closed(p, l)); Qd = Qd_closed(p, l)
    g = lambda j: 1 / (xi ** (p - j) - 1)
    rest = Fr(0)
    for j in range(0, l + 1):
        for m in range(3):
            if j + m - l != p:
                rest += (-1) ** j * comb(l, j) * C[m] * g(j + m - l)
    phi0_A = -Q / 2 + rest            # constant part of Phi0_l
    phi0_B = Qd                       # coefficient of 1/L
    w = Fr(1, l + 1) + Fr(1, l + 2)
    return R * phi0_A, R * (phi0_B - w * Q), phi0_A, phi0_B

ok = True
for xi in (Fr(1, 2), Fr(3, 7), Fr(9, 28), Fr(2, 3), Fr(3, 31)):
    A2_, B2_ = F_parts(2, 0, xi)[:2]
    ok &= (A2_, B2_) == (Fr(-1, 2) - 1 / (1 - xi ** 2) - 4 / (1 - xi), Fr(3))
    A1_, B1_ = F_parts(1, 0, xi)[:2]
    ok &= (A1_, B1_) == (Fr(-3), Fr(-5))
    A0_, B0_ = F_parts(0, 0, xi)[:2]
    ok &= (A0_, B0_) == (Fr(-1, 2) + 4 * xi / (1 - xi) + xi ** 2 / (1 - xi ** 2), Fr(-3, 2))
rep(ok, "A3 F_0 at p = 2, 1, 0 from Lemma 4.2 (c) equals the printed forms exactly (xi = 1/2, 3/7, 9/28, 2/3, 3/31)")

ok = (Q_dual(0, 1)[0] == 1 and Q_dual(0, 2)[0] == 1 and Q_dual(1, 1)[0] == 5
      and mp.gamma(1) * mp.gamma(2) / 2 == mp.mpf(1) / 2 and mp.gamma(2) * mp.gamma(1) / 2 == mp.mpf(1) / 2)
rep(ok, "A4 unmet poles: H(1) = H(2) = 1/2, Q_0 = 1, Q_1(1) = 5, so u^-1/(2L) at p = 1 and (u^-2 + 5u^-1)/(2L) at p = 2")

# H's finite part at -l: compare with psi(l+1) - psi(l+3) numerically
mp.mp.dps = 40
ok = True
for l in range(0, 30):
    R = (-1) ** l * comb(l + 2, 2)
    ok &= abs(R * (mp.digamma(l + 1) - mp.digamma(l + 3)) - (-R * (mp.mpf(1) / (l + 1) + mp.mpf(1) / (l + 2)))) < mp.mpf(10) ** -35
rep(ok, "A5 H^0_l = R_l (psi(l+1) - psi(l+3)) = -R_l (1/(l+1) + 1/(l+2)) (l 0..29)")

# the k = 4 chain, the bridge and Archimedes
ys, bs = [1], [1]                      # y + b sqrt3 = (1 + sqrt3)(2 + sqrt3)^j
for _ in range(10):
    y, b = ys[-1], bs[-1]
    ys.append(2 * y + 3 * b); bs.append(y + 2 * b)
ok = all(y * y - 3 * b * b == -2 for y, b in zip(ys, bs))
ok &= bs[:8] == [1, 3, 11, 41, 153, 571, 2131, 7953] and ys[:6] == [1, 5, 19, 71, 265, 989]
ok &= 265 ** 2 - 3 * 153 ** 2 == -2 and (ys[4], bs[4]) == (265, 153)
p, lam = -74, 359                      # the pair (p_5, lambda_4) of Proposition 4.4 (d)
U, V = 5 - 2 * p, 2 * (lam + p) + 1
ok &= (U, V) == (153, 571) and V - 2 * U == 265 and U * U - 4 * U * V + V * V == -2 and Q_dual(lam + p, -lam)[0] == 0
ok &= 265 ** 2 < 3 * 153 ** 2 and 1351 ** 2 > 3 * 780 ** 2 and 1351 ** 2 - 3 * 780 ** 2 == 1
ok &= 780 not in bs and 1351 not in ys
rep(ok, "A6 Archimedes: (y, b) = (265, 153) is the j = 4 member of y^2 - 3b^2 = -2; at p = -74, l = 359, (U, V) = (153, 571) and V - 2U = 265;"
        " 265/153 < sqrt3 < 1351/780 (by squares); 1351^2 - 3*780^2 = 1, so the upper bound is not on the -2 chain")

# A11: Davies (arXiv:1101.0492v1, Table 2, p. 4) lists the -2 rows 5/3, 19/11, 71/41, 265/153, 989/571 and the +1 rows 7/4, 26/15,
# 97/56, 362/209, 1351/780. The -2 rows are the chain members j = 1..5; no +1 row is a chain member. And the ratios in Heath's two
# figures of Proposition 3 are sqrt3 : 1 (OA : AC with angle AOC 30 degrees; AC : CB with angle CAB 30 degrees, angle C right).
davies_m2 = [(5, 3), (19, 11), (71, 41), (265, 153), (989, 571)]
davies_p1 = [(7, 4), (26, 15), (97, 56), (362, 209), (1351, 780)]
ok = davies_m2 == list(zip(ys[1:6], bs[1:6]))
ok &= all(a * a - 3 * b * b == -2 for a, b in davies_m2) and all(a * a - 3 * b * b == 1 for a, b in davies_p1)
ok &= not any((a, b) in set(zip(ys, bs)) for a, b in davies_p1)
r1 = 1 / mp.tan(mp.pi / 6)                      # OA : AC
r2 = mp.cos(mp.pi / 6) / mp.sin(mp.pi / 6)      # AC : CB in the right triangle ACB
ok &= abs(r1 - mp.sqrt(3)) < mp.mpf(10) ** -30 and abs(r2 - mp.sqrt(3)) < mp.mpf(10) ** -30
rep(ok, "A11 Davies' Table 2: its -2 rows are the chain members j = 1..5 and its +1 rows (1351/780 among them) are not on the chain;"
        " both of Heath's ratios in Proposition 3 equal sqrt3 : 1")

# A12: the other side of the mirror, exact in Z[sqrt3] as integer pairs (a, c) for a + c sqrt3, j = 0..60
ok, a, c = True, 1, 0
for j in range(0, 61):
    ac = (a, -c)                                         # (2 - sqrt3)^j as the conjugate pair
    ok &= a * a - 3 * c * c == 1                         # (2 + sqrt3)^j (2 - sqrt3)^j = 1
    ok &= (a + ac[0], c + ac[1]) == (2 * a, 0)           # the sqrt3 parts cancel: the sum is 2 a_j, whole
    b, y = a + c, a + 3 * c                              # (1 + sqrt3)(a + c sqrt3) = (a + 3c) + (a + c) sqrt3
    ok &= (j > 10 or (y, b) == (ys[j], bs[j])) and y * y - 3 * b * b == -2
    a, c = 2 * a + 3 * c, a + 2 * c                      # times (2 + sqrt3)
ok &= (2 * 2 - 3 * 1 * 1) == 1
rep(ok, "A12 the other side: (2+sqrt3)(2-sqrt3) = 1; with (2+sqrt3)^j = a_j + c_j sqrt3, (2+sqrt3)^j + (2-sqrt3)^j = 2a_j and a_j^2 - 3c_j^2 = 1;"
        " b_j = a_j + c_j, y_j = a_j + 3c_j, y_j^2 - 3b_j^2 = -2 (j 0..60; equal to the chain for j <= 10)")

# A13: the horizon arithmetic of Section 6.8 (a): at the five classically stable points the quoted kappa = (q/xi)^2 and the
# per-pass ratio q/xi^2 (RESULT_T7b.md lines 125 to 126), kappa < 1 and ratio > 1; and q/xi^2 = r under r = q xi^-2, so ratio 1 is p = 0
pts5 = [((Fr(2, 100), Fr(5, 1000)), Fr(625, 10000), Fr(125, 10)), ((Fr(5, 100), Fr(5, 1000)), Fr(1, 100), Fr(2)),
        ((Fr(1, 10), Fr(5, 100)), Fr(25, 100), Fr(5)), ((Fr(2, 10), Fr(5, 100)), Fr(625, 10000), Fr(125, 100)),
        ((Fr(3, 10), Fr(2, 10)), Fr(4, 9), Fr(20, 9))]
ok = True
for (xi_, q_), kap, rat in pts5:
    ok &= (q_ / xi_) ** 2 == kap and q_ / xi_ ** 2 == rat and kap < 1 < rat and xi_ * xi_ < q_
ok &= abs(mp.mpf(4) / 9 - mp.mpf("0.444")) < 1e-3 and abs(mp.mpf(20) / 9 - mp.mpf("2.22")) < 1e-2
rep(ok, "A13 horizon: the five classically stable points have kappa = (q/xi)^2 < 1 and ratio q/xi^2 > 1 (1.25 to 12.5); with r = q xi^-2 the ratio is r")

# A14: eq. 14's arithmetic with CODATA 2018: (l_P/D)(m_P/l_P^3) at D = 1 m, in g/cm^3, and the gap to the printed 1e49
lP_cm, mP_g, D_cm = mp.mpf("1.616255e-33"), mp.mpf("2.176434e-5"), mp.mpf(100)
val = (lP_cm / D_cm) * (mP_g / lP_cm ** 3)
gap = mp.log10(val) - 49
ok = abs(val / mp.mpf("8.33e58") - 1) < 1e-3 and abs(gap - mp.mpf("9.92")) < 0.005
rep(ok, "A14 eq. 14: (l_P/D)(m_P/l_P^3) at D = 1 m = " + mp.nstr(val, 4) + " g/cm^3, " + mp.nstr(gap, 4) + " decades above the printed 1e49")

# A16: the appendix identity at 40 digits
lhs = mp.nsum(lambda m: mp.zeta(2 * m) / ((2 * m + 1) * mp.mpf(4) ** m), [1, mp.inf])
mid = mp.quad(lambda t: 1 - mp.pi * t * mp.cot(mp.pi * t) if t != 0 else mp.mpf(0), [0, mp.mpf(1) / 2])
rhs = (1 - mp.log(2)) / 2
lead = -mp.log(mp.log(2))
half = mp.quad(lambda t: mp.pi * t * mp.cot(mp.pi * t) if t != 0 else mp.mpf(1), [0, mp.mpf(1) / 2])
ok = abs(lhs - rhs) < mp.mpf(10) ** -35 and abs(mid - rhs) < mp.mpf(10) ** -35 and abs(half - mp.log(2) / 2) < mp.mpf(10) ** -35
ok &= abs(lead - mp.mpf("0.3665")) < 1e-4 and abs(mp.log(10) / 4 - mp.mpf("0.5756")) < 1e-4
rep(ok, "A16 sum zeta(2m)/((2m+1)4^m) = int_0^1/2 (1 - pi t cot pi t) dt = (1 - ln2)/2 = " + mp.nstr(rhs, 12) + "; int pi t cot pi t = ln2/2;"
        " -ln(ln 2) = " + mp.nstr(lead, 6) + "; (1/4) ln 10 = " + mp.nstr(mp.log(10) / 4, 6))

# figure data
def read_dat(name):
    rows = open(os.path.join(FIG, name), encoding="utf-8").read().split("\n")
    return [tuple(float(v) for v in r.split()) for r in rows[1:] if r.strip()]

def stairs(k, count):                  # walk from (1, k) by T then S, alternately, as (2 - p, l)
    pts, p, l = [], 1, k
    pts.append((2 - p, l))
    while len(pts) < count:
        p = 2 - l - p; pts.append((2 - p, l))                     # S: the other p at the same l
        if len(pts) < count:
            l = 2 * k + 1 - (k + 2) * p - l; pts.append((2 - p, l))   # T: the other l at the same p
    return pts

ok = True
for k, name in ((2, "r2_stairs_k2.dat"), (3, "r2_stairs_k3.dat"), (4, "r2_stairs_k4.dat")):
    d = read_dat(name)
    st = stairs(k, len(d))
    ok &= [(int(a), int(b)) for a, b in d] == st
    for t, l in st:                    # every corner a zero of Q_n(-l) with weights 1, k, 1, from the definition
        pp = 2 - t
        ok &= Q_dual(l + pp, -l, (1, k, 1))[0] == 0
rep(ok, "A7 the staircase data (k = 2, 3, 4) equal the walk by S and T from (1, k), and Q_n(-l) = 0 at every corner from the definition")

pts = read_dat("r2_bridge_pts.dat")
ok = all(int(u) ** 2 - 4 * int(u) * int(v) + int(v) ** 2 == -2 for u, v in pts) and len(pts) == 11
cur = read_dat("r2_bridge_curve.dat")
# The file prints 10 significant digits (first try, kept: a flat 1e-12 bar failed at 5.2e-10, the rounding of the print).
# Bar per point: the residual's change under a rounding of at most half a unit in the 10th digit of U and of V.
def rnd(v):
    from math import floor, log10
    return 0.5 * 10 ** (floor(log10(abs(v))) - 9)
over, worst = 0, 0.0
for u, v in cur:
    eu, ev = rnd(u), rnd(v)
    bound = abs(2 * u - 4 * v) * eu + abs(2 * v - 4 * u) * ev + 6 * eu * ev + 1e-12 * (u * u + v * v)
    res = abs(u * u - 4 * u * v + v * v + 2)
    worst = max(worst, res / bound); over += res > bound
ok &= over == 0
rep(ok, "A8 bridge figure: the 11 dots lie exactly on U^2 - 4UV + V^2 = -2; every drawn curve point lies on it within its own 10-digit rounding",
    f"curve points {len(cur)}, worst residual {worst:.2f} of its rounding bound")

# the slide as a parametrization of the conic branch, k = 3..10
ok, worst = True, 0.0
for k in range(3, 11):
    th = mp.acosh(mp.mpf(k) / 2)
    X = lambda s: mp.cosh((s - mp.mpf(1) / 2) * th) / mp.cosh(th / 2)
    u = [1, 1]
    for _ in range(12): u.append(k * u[-1] - u[-2])
    for i in range(0, 12):
        ok &= abs(X(i) - u[i]) / u[i] < mp.mpf(10) ** -30
    for s in (mp.mpf("0.3"), mp.mpf("1.7"), mp.mpf("4.45"), mp.mpf("9.9")):
        a, b = X(s), X(s + 1)
        r = abs(a * a - k * a * b + b * b - (2 - k)) / (a * a + b * b)
        worst = max(worst, float(r))
ok &= worst < 1e-30
rep(ok, "A9 X(s) = cosh((s - 1/2) theta)/cosh(theta/2), cosh theta = k/2: X(i) = u_i at whole i, and (X(s), X(s+1)) stays on U^2 - kUV + V^2 = 2 - k (k 3..10)",
    f"worst scaled residual {worst:.1e}")

# F-056: weights c0, c1, c2
ok, cnt = True, 0
for c in ((1, 4, 1), (1, 3, 1), (1, 4, 2), (2, 5, 1), (1, 2, 3), (3, 7, 3)):
    for p in range(-30, 2):
        for l in range(max(0, -p), 201):
            t, x = 2 - p, l + p
            cond = c[0] * t * (t - 1) - c[1] * t * x + c[2] * x * (x - 1) == 0
            ok &= (Q_dual(l + p, -l, c)[0] == 0) == cond
            cnt += 1
rep(ok, "A10 weights c0, c1, c2: Q_{p+l}(-l) = 0 exactly when c0 t(t-1) - c1 t x + c2 x(x-1) = 0 (six weight sets, p -30..1, l <= 200)", f"{cnt} values")

# A17 (r5c): the chains of the rewritten remark on general weights. With (t, x) = (2 - p, l + p) the condition is
# c0 t(t-1) - c1 t x + c2 x(x-1) = 0, and its two Vieta jumps are x' = (c1 t + c2 (1 - x))/c2 at fixed t and
# t' = (c1 x + c0 (1 - t))/c0 at fixed x. Q_int is the definition of Q_n in exact integers (binom(z, j) at an integer z is an
# integer), tied first to Q_dual on the A10 window at both weight sets.
def Q_int(n, s, c):
    v = 0
    for m in range(0, min(2, n) + 1):
        z, j, num = s + n - m - 1, n - m, 1
        for i in range(j):
            num *= z - i
        v += c[m] * (num // factorial(j))
    return v

def quad(c, t, x):
    return c[0] * t * (t - 1) - c[1] * t * x + c[2] * x * (x - 1)

def arm(c, first, steps):              # from (t, x) = (0, 0), the two jumps alternately, the first 't' or 'x'; stops at a non-integer root
    t, x, which, pts = 0, 0, first, []
    for _ in range(steps):
        if which == "t":
            num = c[1] * x + c[0] * (1 - t)
            if num % c[0]: return pts, Fr(num, c[0])
            t, which = num // c[0], "x"
        else:
            num = c[1] * t + c[2] * (1 - x)
            if num % c[2]: return pts, Fr(num, c[2])
            x, which = num // c[2], "t"
        pts.append((t, x))
    return pts, None

def pl(pts):                           # the members in range (t >= 1, x >= 0, t + x >= 2), as (p, l)
    return [(2 - t, x + t - 2) for t, x in pts if t >= 1 and x >= 0 and t + x >= 2]

def zeros_window(c, plo, phi, lmax):   # every in-range zero of the quadratic, by evaluation at every (p, l) of the window
    return {(p, l) for p in range(plo, phi + 1) for l in range(max(0, -p), lmax + 1) if quad(c, 2 - p, l + p) == 0}

def zeros_disc(c, plo, phi, lmax):     # the same zeros, by solving the quadratic in x exactly at each p
    out = set()
    for p in range(plo, phi + 1):
        t = 2 - p
        b = c[2] + c[1] * t
        D = b * b - 4 * c[2] * c[0] * t * (t - 1)
        if D < 0: continue
        r = isqrt(D)
        if r * r != D: continue
        for num in {b + r, b - r}:
            if num % (2 * c[2]) == 0:
                x = num // (2 * c[2]); l = x - p
                if x >= 0 and 0 <= l <= lmax: out.add((p, l))
    return out

ARM_A = [(1, 2), (-10, 13), (-10, 32), (-75, 97), (-75, 208), (-454, 587), (-454, 1234), (-2663, 3443), (-2663, 7214)]
ARM_B = [(-3, 4), (-3, 13), (-34, 44), (-34, 97), (-215, 278), (-215, 587), (-1270, 1642), (-1270, 3443)]
ORB_9 = [(-8, 9), (-8, 53), (-394, 439), (-394, 2132), (-15245, 16983)]
c42, c92 = (1, 4, 2), (1, 9, 2)
ok = all(Q_int(l + p, -l, c) == Q_dual(l + p, -l, c)[0] for c in (c42, c92) for p in range(-30, 2) for l in range(max(0, -p), 201))
a, enda = arm(c42, "t", 10); b, endb = arm(c42, "x", 9)
ok &= pl(a) == ARM_A and pl(b) == ARM_B and enda is None and endb is None
o1, end1 = arm(c92, "t", 50); o2, end2 = arm(c92, "x", 50)
ok &= pl(o1) == [] and end1 == Fr(11, 2) and pl(o2) == ORB_9 and end2 == Fr(133749, 2)
members = [(c42, q) for q in ARM_A + ARM_B] + [(c92, q) for q in ORB_9]
ok &= len(members) == 22 and all(quad(c, 2 - p, l + p) == 0 and Q_int(l + p, -l, c) == 0 for c, (p, l) in members)
win = [q for q in ARM_A + ARM_B if q[0] >= -300 and q[1] <= 3000]
z42 = zeros_window(c42, -300, 1, 3000)
ok &= len(win) == 11 and z42 == set(win) and zeros_disc(c42, -300, 1, 3000) == z42
z92 = zeros_window(c92, -300, 1, 3000)
ok &= z92 == {(-8, 9), (-8, 53)} and zeros_disc(c92, -300, 1, 3000) == z92
far = zeros_disc(c42, -2700, -301, 7300)
ok &= len(far) == 6 and far == {q for q in ARM_A + ARM_B if -2700 <= q[0] <= -301 and q[1] <= 7300}
# the third jump: along t + x = l + 2 the root sum in x is (c0 (2l+3) + c1 (l+2) + c2)/(c0 + c1 + c2), (6l+13)/7 at (1,4,2)
shared = sorted(set(l for p, l in ARM_A) & set(l for p, l in ARM_B))
ok &= shared == [13, 97, 587, 3443]
for l in shared:
    xs = [l + p for p, ll in ARM_A + ARM_B if ll == l]
    num = c42[0] * (2 * l + 3) + c42[1] * (l + 2) + c42[2]
    ok &= len(xs) == 2 and num == 6 * l + 13 and num % 7 == 0 and sum(xs) == num // 7
rep(ok, "A17 the chains of the remark on general weights: at (1,4,2) the two Vieta-jump arms from (0,0) equal the printed lists (9 and 8"
        " members) and are the only zeros in -300 <= p <= 1, l <= 3000 (11) and in -2700 <= p <= -301, l <= 7300 (6, the quadratic"
        " solved at each p); at (1,9,2) the orbit is the printed 5, its ends at x = 11/2 and 133749/2, and the first window holds"
        " (-8, 9) and (-8, 53) only; Q_{p+l}(-l) = 0 from the definition at all 22; the third jump's root sum (6l+13)/7 at"
        " l = 13, 97, 587, 3443", f"{len(members)} members, {len(far)} far zeros")

# A18 (r5d): the descent at (1,4,2) in the remark on general weights. Every zero with t, x >= 0 and -3000 <= p <= 1 (all l, found by
# solving the quadratic in x exactly at each p); while t, x >= 1, the fixed-x jump t' = 4x + 1 - t lowers t when t^2 > 2x(x-1), and the
# fixed-t jump x' = 2t + 1 - x lowers x when x^2 > t(t-1)/2. One of the two must hold, the new point must be a zero with nonnegative
# whole coordinates and a smaller t + x, and the run must end at (0,0), (0,1) or (1,0).
zs = set()
for p in range(-3000, 2):
    t = 2 - p
    b = c42[2] + c42[1] * t
    D = b * b - 4 * c42[2] * c42[0] * t * (t - 1)
    r = isqrt(D) if D >= 0 else -1
    if r >= 0 and r * r == D:
        for num in {b + r, b - r}:
            if num >= 0 and num % (2 * c42[2]) == 0:
                zs.add((t, num // (2 * c42[2])))
ok, longest = True, 0
for ta, xa in sorted(zs):
    t, x, steps = ta, xa, 0
    while t >= 1 and x >= 1:
        if t * t > 2 * x * (x - 1):
            t2, x2 = 4 * x + 1 - t, x
        elif 2 * x * x > t * (t - 1):
            t2, x2 = t, 2 * t + 1 - x
        else:
            ok = False; break
        ok &= t2 >= 0 and x2 >= 0 and t2 + x2 < t + x and quad(c42, t2, x2) == 0
        t, x, steps = t2, x2, steps + 1
    ok &= (t, x) in {(0, 0), (0, 1), (1, 0)}
    longest = max(longest, steps)
inrange = {(2 - t, x + t - 2) for t, x in zs if t >= 1 and x >= 0 and t + x >= 2}
ok &= inrange == {q for q in ARM_A + ARM_B if q[0] >= -3000} and len(inrange) == 17
rep(ok, f"A18 the descent at (1,4,2): from each of the {len(zs)} zeros with t, x >= 0 and -3000 <= p <= 1 (all l), one of the two jumps"
        " always lowers t + x to a zero with nonnegative whole coordinates, and every run ends at (0,0), (0,1) or (1,0); the zeros in range"
        " are exactly the 17 chain members with p >= -3000", f"longest run {longest} steps")

# A19 (r5d): at (1,9,2) the orbit of (0,0) is not all of the zeros (finding 4 of the gate check of r5d). (t, x) = (12297247, 53935738)
# is a zero with t odd and t^2 < 2x(x-1): its fixed-t jump, the one that lowers, is a half-integer, and its fixed-x jump climbs to
# (473124396, 53935738), then the fixed-t jump to (473124396, 2075124045), both zeros. Q_{p+l}(-l) there by its closed form for p <= 0,
# (-1)^n binom(l, n) [c0 - c1 n/(l-n+1) + c2 n(n-1)/((l-n+1)(l-n+2))], the bracket in exact rationals (the raw binomials have about
# 14 million digits).
t9, x9 = 12297247, 53935738
ok = quad(c92, t9, x9) == 0 and t9 % 2 == 1 and t9 * t9 < 2 * x9 * (x9 - 1)
xj = Fr(c92[1] * t9 + c92[2] * (1 - x9), c92[2])
ok &= xj.denominator == 2 and xj < x9
tu = c92[1] * x9 + c92[0] * (1 - t9)
xu = Fr(c92[1] * tu + c92[2] * (1 - x9), c92[2])
ok &= tu == 473124396 and quad(c92, tu, x9) == 0 and xu == 2075124045 and quad(c92, tu, 2075124045) == 0
p9, l9 = 2 - t9, x9 + t9 - 2
n9 = p9 + l9
br = c92[0] - Fr(c92[1] * n9, l9 - n9 + 1) + Fr(c92[2] * n9 * (n9 - 1), (l9 - n9 + 1) * (l9 - n9 + 2))
ok &= (p9, l9) == (-12297245, 66232983) and br == 0 and (t9, x9) not in set(o1) | set(o2) | {(0, 0)}
rep(ok, "A19 at (1,9,2) the orbit of (0,0) is not all of the zeros: (t, x) = (12297247, 53935738), (p, l) = (-12297245, 66232983), is a"
        " zero (the bracket of Q_n(-l) is 0 in exact rationals) with t odd and t^2 < 2x(x-1), its lowering jump the half-integer"
        f" x' = {xj}, and its chain climbs through (473124396, 53935738) and (473124396, 2075124045)")

# ---------------- B. numerical, 40 digits ----------------
mp.mp.dps = 40

def mpq(x):                           # a Fraction as an mpf
    return mp.mpf(x.numerator) / x.denominator

def Phi_cont(s, xi, p, c=C):          # Phi = sum_n Q_n rho_n, with b_j(s) = binom(s + j - 1, j) by its recurrence
    L = mp.log(1 / mpq(xi)); tot = mp.mpc(0)
    lim = int(mp.re(p - s)) + int(50 * mp.log(10) / L) + 60
    b = [mp.mpc(1)]
    for j in range(1, lim + 1):
        b.append(b[-1] * (s + j - 1) / j)
    for n in range(0, lim + 1):
        Qn = sum(c[m] * b[n - m] for m in range(0, min(2, n) + 1))
        tot += Qn / (mp.exp(L * (n + s - p)) - 1)
    return tot

def H(s):
    return mp.gamma(s) * mp.gamma(3 - s) / 2

worstF, worstG, cnt = 0.0, 0.0, 0
for xi in (Fr(1, 2), Fr(2, 3)):
    L = mp.log(1 / mpq(xi))
    for p in (-3, -1, 0, 1, 2):
        for l in range(max(0, -p), max(0, -p) + 5):
            N, d = 96, mp.mpf(1) / 4
            Fc = Gc = mp.mpc(0)
            for i in range(N):
                e = d * mp.expjpi(2 * mp.mpf(i) / N)
                v = H(-l + e) * Phi_cont(-l + e, xi, p) * e / N
                Fc += v; Gc += v * e
            A, B = F_parts(p, l, xi)[:2]
            Fcl = mp.mpf(A.numerator) / A.denominator + (mp.mpf(B.numerator) / B.denominator) / L
            Gcl = (-1) ** l * comb(l + 2, 2) * Q_closed(p, l) / L
            rf = abs(Fc - Fcl) / max(abs(Fcl), mp.mpf(1))
            rg = abs(Gc - Gcl) / max(abs(Gcl), mp.mpf(1))
            worstF, worstG = max(worstF, float(rf)), max(worstG, float(rg)); cnt += 1
rep(worstF < 1e-25 and worstG < 1e-25,
    "B1 F_l and G_l from Lemma 4.2 (c) against the Laurent coefficients of H Phi read off a circle of radius 1/4 (96 points) around -l, Phi by the continuation series",
    f"{cnt} (xi, p, l), worst {worstF:.1e} for F and {worstG:.1e} for G (relative, or absolute below 1)")

worst2, cnt = 0.0, 0
for xi in (Fr(1, 2), Fr(2, 3)):
    L = mp.log(1 / mpq(xi))
    for p in (-2, 0, 1, 2):
        for l in (8, 12, 20):
            if l < max(1, -p): continue
            _, _, a0, b0 = F_parts(p, l, xi)
            first = mp.mpf(a0.numerator) / a0.denominator + (mp.mpf(b0.numerator) / b0.denominator) / L
            s1 = mp.mpf(0)
            for m in range(3):
                if m >= p and m - p <= l:
                    s1 += C[m] * (-1) ** (l + p - m) * comb(l, m - p) * (mp.harmonic(l + p - m) - mp.harmonic(l))
                elif m - p > l:
                    s1 += C[m] * mp.factorial(l) * mp.factorial(m - p - l - 1) / mp.factorial(m - p)
            s1 /= L
            s2 = mp.mpc(0)
            for m in range(3):
                q = p - m
                for k in range(1, 401):
                    tau = 2 * mp.pi * k / L
                    for sg in (1, -1):
                        s2 += C[m] * mp.gamma(q - 1j * sg * tau) / mp.gamma(l + 1 + q - 1j * sg * tau)
            second = s1 + (-1) ** (l + 1) * mp.factorial(l) / L * s2
            r = abs(second - first) / max(abs(first), mp.mpf(1))
            worst2 = max(worst2, float(r)); cnt += 1
rep(worst2 < 1e-15, "B2 the two closed forms of Phi^0_l agree (l = 8, 12, 20; the k-sum to 400 shells, no tail)", f"{cnt} (xi, p, l), worst {worst2:.1e}")

# B3 (r5d): Claim 3.1 as written out in Section 1.3. On re s > p the direct sum Phi = sum_N a_N b_N^-s equals the continuation series
# sum_n Q_n rho_n (Phi_cont); and at points s_{n,k} = p - n - i tau_k of P the residue of the series, read off a circle of radius 1/4
# (96 points), equals Q_n(s_{n,k})/L, with binom(z, j) from its product definition.
def Phi_direct(s, xi, p, c=C):
    x = mpq(xi); r = x ** (-p); tot = mp.mpc(0); N = 0
    while True:
        N += 1
        w = x ** N
        term = r ** N * (c[0] + c[1] * w + c[2] * w * w) * (1 / w - 1) ** (-s)
        tot += term
        if N > 5 and abs(term) < mp.mpf(10) ** -50 * max(abs(tot), 1):
            return tot

def Q_mp(n, s, c=C):
    return sum(c[m] * mp.fprod(s + n - m - 1 - i for i in range(n - m)) / mp.factorial(n - m) for m in range(0, min(2, n) + 1))

worst3, worst4, cnt3, cnt4 = 0.0, 0.0, 0, 0
for xi in (Fr(1, 2), Fr(2, 3)):
    L = mp.log(1 / mpq(xi))
    for p in (mp.mpf(-3), mp.mpf("-1.3"), mp.mpf("0.4"), mp.mpf("1.7"), mp.mpf(2)):
        for s in (p + mp.mpc("0.6", "1.3"), p + mp.mpc("2.5", "-7")):
            a, b = Phi_direct(s, xi, p), Phi_cont(s, xi, p)
            worst3 = max(worst3, float(abs(a - b) / max(abs(a), mp.mpf(1)))); cnt3 += 1
    for p in (mp.mpf("-1.3"), mp.mpf("0.4"), mp.mpf("1.7")):
        for n, k in ((0, 0), (1, 1), (2, -1), (5, 2)):
            s0 = p - n - 1j * 2 * mp.pi * k / L
            N, d, res = 96, mp.mpf(1) / 4, mp.mpc(0)
            for i in range(N):
                e = d * mp.expjpi(2 * mp.mpf(i) / N)
                res += Phi_cont(s0 + e, xi, p) * e / N
            want = Q_mp(n, s0) / L
            worst4 = max(worst4, float(abs(res - want) / max(abs(want), mp.mpf(1)))); cnt4 += 1
rep(worst3 < 1e-30 and worst4 < 1e-30,
    f"B3 Claim 3.1 as written out in Section 1.3: the direct sum against the continuation series at {cnt3} points with re s > p, and the"
    f" residue of the series at {cnt4} points of P, read off a circle of radius 1/4 (96 points), against Q_n(s_(n,k))/L",
    f"worst {worst3:.1e} and {worst4:.1e} (relative, or absolute below 1)")

# A15 (run last: it uses Phi_cont from part B): p* = the zero of Phi(0) = g0 + 4 g1 + g2 at xi = 1/40 near 1.952, and Phi(0)
# from the continuation series equals that finite form
mp.mp.dps = 40
xi40 = mp.mpf(1) / 40
phi0 = lambda p: sum(Cm / (xi40 ** (p - m) - 1) for m, Cm in enumerate(C))
pstar = mp.findroot(phi0, (mp.mpf("1.951"), mp.mpf("1.953")), solver="anderson")
signs = [mp.sign(phi0(mp.mpf(194) / 100 + mp.mpf(i) / 1600)) for i in range(0, 49)]
changes = sum(1 for i in range(48) if signs[i] != signs[i + 1])
pcheck = mp.mpf("1.9516704581340539208")
cont = Phi_cont(mp.mpc(0), Fr(1, 40), mp.mpf("1.93"))
ok = abs(pstar - pcheck) < mp.mpf(10) ** -18 and changes == 1 and abs(cont - phi0(mp.mpf("1.93"))) < mp.mpf(10) ** -30
rep(ok, "A15 p*: the zero of g0 + 4g1 + g2 at xi = 1/40 is " + mp.nstr(pstar, 22) + " (one sign change on 49 points of [1.94, 1.97]);"
        " Phi(0) by the continuation series equals the finite form at p = 1.93")

lines.append(f"     {len(lines)} checks, {time.time() - t0:.1f} s (machine clock {time.strftime('%Y-%m-%d %H:%M:%S')})")
lines.append("ALL PASS" if not fails else "FAILED: " + ", ".join(fails))
print(lines[-2]); print(lines[-1])
open(OUT, "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")
sys.exit(0 if not fails else 1)
