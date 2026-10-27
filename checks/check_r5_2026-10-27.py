# Checks for the r5 proof-pieces note (2026-10-27): every formula put back from the held list, the k = 4 bridge and
# Archimedes lines, and the figure data. Exact arithmetic (Fraction) in part A; mpmath at 40 digits in part B.
# Prints PASS or FAIL per check and ALL PASS at the end; writes CHECK_r5_2026-10-27.txt beside this file.
import os, sys, time
from fractions import Fraction as Fr
from math import comb, factorial, isqrt
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "CHECK_r5_2026-10-27.txt")
FIG = os.path.join(os.path.dirname(HERE), "fig_r5")
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

lines.append(f"     {len(lines)} checks, {time.time() - t0:.1f} s (machine clock {time.strftime('%Y-%m-%d %H:%M:%S')})")
lines.append("ALL PASS" if not fails else "FAILED: " + ", ".join(fails))
print(lines[-2]); print(lines[-1])
open(OUT, "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")
sys.exit(0 if not fails else 1)
