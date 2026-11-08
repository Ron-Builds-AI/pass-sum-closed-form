# Checks for the r5g proof-pieces note (version 1.4, 2026-11-06): the steps that r5g writes out in full, the identities of the
# whole-shift route that its lineage paragraph cites, and the mapping to Luca and Szalay and the OEIS entries it cites.
# The checker of the formulas of versions 1.1 to 1.4 is check_r5d_2026-10-29.py; this one checks only what r5g adds.
# Part S is symbolic algebra (sympy), part E exact integer arithmetic, part N mpmath at 40 digits. Part N samples points:
# it is evidence beside the proofs, not proof.
# Prints PASS or FAIL per check and ALL PASS at the end; writes CHECK_r5g_2026-11-06.txt beside this file.
import os, time
from math import comb, isqrt
import sympy as sp
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "CHECK_r5g_2026-11-06.txt")
lines, fails = [], []
t0 = time.time()


def rep(ok, name, detail=""):
    s = ("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else "")
    print(s, flush=True)
    lines.append(s)
    if not ok:
        fails.append(name)


def zero(e):
    return sp.expand(e) == 0


# ---------------------------------------------------------------- part S: symbolic
k, t, x, a, c1, s, w = sp.symbols("k t x a c1 s w")

# S1 Proposition B (i), with the three expansions printed in its proof, and the degrees
U = (k - 2) * t + 1
V = (k - 2) * x + 1
lhs = (k - 2) ** 2 * (t ** 2 - k * t * x + x ** 2 - t - x)
rhs = U ** 2 - k * U * V + V ** 2 - (2 - k)
ok = zero(lhs - rhs)
ok &= zero(U ** 2 - ((k - 2) ** 2 * t ** 2 + 2 * (k - 2) * t + 1))
ok &= zero(V ** 2 - ((k - 2) ** 2 * x ** 2 + 2 * (k - 2) * x + 1))
ok &= zero(U * V - ((k - 2) ** 2 * t * x + (k - 2) * (t + x) + 1))
ok &= zero(U ** 2 - k * U * V + V ** 2 - ((k - 2) ** 2 * (t ** 2 - k * t * x + x ** 2) - (k - 2) ** 2 * (t + x) + 2 - k))
ok &= zero(2 * (k - 2) - k * (k - 2) + (k - 2) ** 2)
degs = [tuple(sp.Poly(sp.expand(e), k, t, x).degree(v) for v in (k, t, x)) for e in (lhs, rhs)]
ok &= all(d[0] <= 3 and d[1] <= 2 and d[2] <= 2 for d in degs)
rep(ok, "S1 Proposition B (i): (k-2)^2 (t^2 - ktx + x^2 - t - x) = U^2 - kUV + V^2 - (2-k), and the three expansions of its proof, "
        "symbolically; degrees in (k, t, x) at most (3, 2, 2)", "degrees of the two sides %s" % (degs,))

# S2 Step 3 of Proposition 4.4: the bracket, the quadratic, the discriminant and its three expansions; Proposition W (c); the remark
P = x ** 2 - (4 * a + 9) * x + (a + 1) * (a + 2)
br = (a + 1) * (a + 2) - 4 * (a + 2) * x + x * (x - 1)
ok = zero(br - P) and zero(-4 * (a + 2) * x - x + (4 * a + 9) * x)
ok &= zero((4 * a + 9) ** 2 - 4 * (a + 1) * (a + 2) - (12 * a ** 2 + 60 * a + 73))
ok &= zero((4 * a + 9) ** 2 - (16 * a ** 2 + 72 * a + 81)) and zero(4 * (a + 1) * (a + 2) - (4 * a ** 2 + 12 * a + 8))
ok &= zero(3 * (2 * a + 5) ** 2 - (12 * a ** 2 + 60 * a + 75)) and zero(3 * (2 * a + 5) ** 2 - 2 - (12 * a ** 2 + 60 * a + 73))
ok &= all(sp.Poly(sp.expand(e), a, x).degree(v) <= 2 for e in (br, P) for v in (a, x))
brk = ((a + 1) * (a + 2) - k * (a + 2) * x + x * (x - 1)).subs(a, t - 2)
ok &= zero(brk - (t ** 2 - k * t * x + x ** 2 - t - x))
ok &= zero((c1 * (a + 2) + 1) ** 2 - 4 * (a + 1) * (a + 2) - ((c1 ** 2 - 4) * (a + 2) ** 2 + (2 * c1 + 4) * (a + 2) + 1))
rep(ok, "S2 Step 3 of Proposition 4.4: (a+1)(a+2) - 4(a+2)x + x(x-1) = x^2 - (4a+9)x + (a+1)(a+2), the discriminant 12a^2 + 60a + 73 "
        "= 3(2a+5)^2 - 2 with its expansions, degrees at most 2 in a and x; the bracket of Proposition W (c) at t = a + 2; the "
        "discriminant of the remark at weights (1, c1, 1)")

# S3 Chu-Vandermonde, as used in the whole-shift route of Section 1.4
ok = True
for n in range(1, 8):
    e = sum(sp.binomial(n, r) * sp.rf(1 - s, r) * sp.rf(s - n + w, n - r) for r in range(n + 1)) - sp.rf(1 - n + w, n)
    ok &= zero(sp.expand_func(e))
rep(ok, "S3 Chu-Vandermonde: sum_r C(n,r) (1-s)_r (s-n+w)_(n-r) = (1-n+w)_n, symbolically in s and w", "n = 1 to 7")

# ---------------------------------------------------------------- part E: exact integers
# E1 the descent of Proposition 4.4, Step 4
chain = [(1, 1)]
for _ in range(40):
    y0, b0 = chain[-1]
    chain.append((2 * y0 + 3 * b0, y0 + 2 * b0))


def pell_descent(y0, b0):
    y1, b1, n = y0, b0, 0
    while b1 >= 2:
        y2, b2 = 2 * y1 - 3 * b1, 2 * b1 - y1
        if not (y2 > 0 and 0 < b2 < b1 and y2 * y2 - 3 * b2 * b2 == -2):
            return None
        y1, b1, n = y2, b2, n + 1
    return (y1, b1, n)


ok = all(pell_descent(y0, b0) == (1, 1, j) and j <= b0 - 1 or (j == 0 and b0 == 1) for j, (y0, b0) in enumerate(chain))
sols = [(isqrt(3 * b0 * b0 - 2), b0) for b0 in range(1, 1000001) if isqrt(3 * b0 * b0 - 2) ** 2 == 3 * b0 * b0 - 2]
ok &= all(pell_descent(y0, b0) is not None and pell_descent(y0, b0)[:2] == (1, 1) for (y0, b0) in sols)
ok &= sols == [c for c in chain if c[1] <= 1000000]
rep(ok, "E1 Proposition 4.4, Step 4: from (y_j, b_j) the descent (y, b) -> (2y - 3b, 2b - y) gives a positive solution with a smaller "
        "b at every step and reaches (1, 1) after exactly j steps (j <= 40); every positive solution with b <= 10^6 descends to (1, 1)",
    "%d chain members, %d solutions with b <= 10^6" % (len(chain), len(sols)))

# E2 the descent of Proposition W (d), k = -8 .. 12
ok, nsol, longest = True, 0, 0
for kk in range(-8, 13):
    for tt in range(0, 3001):
        d = (kk * tt + 1) ** 2 - 4 * (tt * tt - tt)
        if d < 0 or isqrt(d) ** 2 != d:
            continue
        for xx in {(kk * tt + 1 + isqrt(d)) // 2, (kk * tt + 1 - isqrt(d)) // 2}:
            if xx < 0 or tt * tt - kk * tt * xx + xx * xx != tt + xx:
                continue
            nsol += 1
            ct, cx, steps, start = tt, xx, 0, tt + xx
            while (ct, cx) != (0, 0):
                if ct >= cx:
                    nt, nx = kk * cx + 1 - ct, cx
                else:
                    nt, nx = ct, kk * ct + 1 - cx
                if not (nt >= 0 and nx >= 0 and nt * nt - kk * nt * nx + nx * nx == nt + nx and nt + nx <= ct + cx - 1):
                    ok = False
                    break
                ct, cx, steps = nt, nx, steps + 1
            ok &= steps <= start
            longest = max(longest, steps)
rep(ok, "E2 Proposition W (d): from every nonnegative solution of (E_k) with t <= 3000, -8 <= k <= 12, the step T or STS lowers t + x "
        "by at least 1 to a nonnegative solution, and the descent ends at (0, 0) within t + x steps",
    "%d solutions, longest descent %d steps" % (nsol, longest))

# E3 Luca and Szalay: their eq. (6) under (A, B, C) = (c0, -c1, c2), (x, y) = (t, x); D = B^2 - 4AC; the range of their Theorem
ps, lam = [2, 1], [-1, 4]
for _ in range(14):
    ps.append(4 * ps[-1] - ps[-2] - 5)
    lam.append(4 * lam[-1] - lam[-2] + 6)
pairs = [(ps[j], lam[j]) for j in range(1, 15)] + [(ps[j + 1], lam[j]) for j in range(1, 15)]
A, B, C = 1, -4, 1
ok = B * B - 4 * A * C == 12
outside = []
for (p, l) in pairs:
    X, Y = 2 - p, l + p
    aa = -p
    ok &= A * X * (X - 1) + B * X * Y + C * Y * (Y - 1) == 0
    if l <= 20000:                     # the binomial form at the smaller pairs only (the integers grow fast)
        bin3 = lambda j: comb(l, j) if 0 <= j <= l else 0
        ok &= bin3(aa) - 4 * bin3(aa + 1) + bin3(aa + 2) == 0
    if not (1 <= aa and aa + 2 <= l - 1):
        outside.append((p, l))
ok &= sorted(outside) == [(-3, 4), (1, 4)]
rep(ok, "E3 Luca and Szalay: at the 28 vanishing pairs with p >= %d, A x(x-1) + B xy + C y(y-1) = 0 with (A, B, C) = (1, -4, 1), "
        "(x, y) = (2 - p, l + p), and C(l,a) - 4C(l,a+1) + C(l,a+2) = 0 with a = -p for l <= 20000; D = B^2 - 4AC = 12; exactly (1, 4) and (-3, 4) "
        "lie outside 1 <= a, a + 2 <= l - 1" % min(p for p, l in pairs), "outside: %s" % sorted(outside))

# E4 the OEIS entries as the search printed them
ok = [2 - ps[j] for j in range(7)] == [0, 1, 5, 20, 76, 285, 1065]                       # A061278
ok &= [lam[j] + 3 for j in range(7)] == [2, 7, 26, 97, 362, 1351, 5042]                 # A001075
ok &= [5 - 2 * ps[j] for j in range(7)] == [1, 3, 11, 41, 153, 571, 2131]               # A001835 from its second term
ok &= all(((lam[j] + 3) ** 2 - 1) % 3 == 0 and isqrt(((lam[j] + 3) ** 2 - 1) // 3) ** 2 == ((lam[j] + 3) ** 2 - 1) // 3
          for j in range(15))
z = [0, 0]
for _ in range(14):
    z.append(4 * z[-1] - z[-2] + 1)
a061278 = z[1:]
ok &= all(u * u - u + v * v - v - 4 * u * v == 0 for u, v in zip(a061278, a061278[1:]))
fib = [0, 1]
for _ in range(40):
    fib.append(fib[-1] + fib[-2])
a027941 = [fib[2 * n + 1] - 1 for n in range(12)]
ok &= a027941[:6] == [0, 1, 4, 12, 33, 88]
ok &= all(u * u - u + v * v - v - 3 * u * v == 0 for u, v in zip(a027941, a027941[1:]))
bad4 = [(u, v) for u, v in zip(a027941, a027941[1:]) if u * u - u + v * v - v - 4 * u * v != 0]
ok &= bad4 == list(zip(a027941, a027941[1:]))[1:]
rep(ok, "E4 OEIS: 2 - p_j is A061278, lambda_j + 3 is A001075 (each the x of x^2 - 3y^2 = 1), b_j is A001835 from its second term; "
        "consecutive A061278 terms lie on u^2 - u + v^2 - v - 4uv = 0 (McSorley's comment), and consecutive A027941 terms on the "
        "same with 3uv, while 4uv fails at every pair after (0, 1)", "%d pairs fail with 4uv" % len(bad4))

# ---------------------------------------------------------------- part N: 40 digits, sampled
mp.mp.dps = 40


def absratio(z1, z2):            # |Gamma(z1) / Gamma(z2)|
    return mp.exp(mp.re(mp.loggamma(z1) - mp.loggamma(z2)))


# N1 Lemma L, the horizontal sides: |Gamma(z)/Gamma(1+z-s)| <= 3 2^(M+Lambda+1+|sigma|) e^(pi|t|/2) |y|^(sigma-1)
ok, rows = True, []
for (sv, M, Lam, xi) in [(mp.mpc("-0.3", "0.7"), 2, 3, mp.mpf(1) / 2), (mp.mpc("-2.5", "-1.2"), 5, 8, mp.mpf(3) / 14),
                         (mp.mpc("-0.05", "3.0"), 3, 2, mp.mpf(3) / 4)]:
    L = mp.log(1 / xi)
    sig, tt = mp.re(sv), mp.im(sv)
    Cc = 3 * mp.mpf(2) ** (M + Lam + 1 + abs(sig)) * mp.exp(mp.pi * abs(tt) / 2)
    maxima = []
    for target in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        kap = int(mp.ceil(target * L / (2 * mp.pi)))
        mx = mp.mpf(0)
        for sgn in (1, -1):
            yv = tt + sgn * 2 * mp.pi / L * (kap + mp.mpf(1) / 2)
            for i in range(41):
                xv = -M - mp.mpf(1) / 2 + (Lam + M + mp.mpf(1) / 2) * i / 40
                zz = mp.mpc(xv, yv)
                r = absratio(zz, 1 + zz - sv) / abs(yv) ** (sig - 1)
                mx = max(mx, r)
        maxima.append(mx)
    ok &= all(m_ <= Cc for m_ in maxima) and max(maxima) / min(maxima) < 2
    rows.append("s=%s: max %s, bound %s" % (mp.nstr(sv, 3), mp.nstr(max(maxima), 3), mp.nstr(Cc, 3)))
rep(ok, "N1 Lemma L, horizontal sides: |Gamma(z)/Gamma(1+z-s)| / |y|^(sigma-1) over 41 points of each side, |y| near 10^3 to 10^6, "
        "stays below 3 2^(M+Lambda+1+|sigma|) e^(pi|t|/2) and does not grow with the height (3 cases)", "; ".join(rows))

# N2 Theorem P3, Step 5: the sum over |y_k| > Y against 2(1 + LY/(2 pi (beta - 1))) <= 2 + LY/pi, by the Hurwitz zeta function
ok, worst, ncase = True, mp.mpf(0), 0
for L in (mp.log(2), mp.log(mp.mpf(14) / 3), mp.mpf(3), mp.mpf(8)):
    h = 2 * mp.pi / L
    for tt in (mp.mpf("-17.3"), mp.mpf("-0.4"), mp.mpf(0), mp.mpf("2.2"), mp.mpf("11.9")):
        kmin, kmax = int(mp.floor((-60 - tt) / h)) - 1, int(mp.ceil((60 - tt) / h)) + 1
        cnt = {}
        for kk in range(kmin, kmax + 1):
            yk = abs(tt + h * kk)
            if yk < 50:
                # a point on an end jh belongs to [jh, (j+1)h); without the 1e-30 the rounding of |t + hk|/h at t = 0 put such
                # points one interval low (the first run of this checker failed here, at L = 8, t = 0, a count of 4)
                j = int(mp.floor(yk / h + mp.mpf("1e-30")))
                cnt[j] = cnt.get(j, 0) + 1
        ok &= max(cnt.values()) <= 2
        for Y in (mp.mpf(3), mp.mpf("5.5"), mp.mpf(20), mp.mpf(100)):
            for beta in (mp.mpf(2), mp.mpf("2.5"), mp.mpf(5)):
                k0 = int(mp.floor((Y - tt) / h)) + 1
                v0 = tt + h * k0
                k1 = int(mp.ceil((-Y - tt) / h)) - 1
                w0 = -(tt + h * k1)
                S = (Y / h) ** beta * (mp.zeta(beta, v0 / h) + mp.zeta(beta, w0 / h))
                bound = 2 * (1 + L * Y / (2 * mp.pi * (beta - 1)))
                ok &= v0 > Y and w0 > Y and S <= bound and bound <= 2 + L * Y / mp.pi
                worst = max(worst, S / bound)
                ncase += 1
rep(ok, "N2 Theorem P3, Step 5: at most two |y_k| in each interval [hj, h(j+1)), and the sum of (|y_k|/Y)^(-beta) over |y_k| > Y, "
        "exact through the Hurwitz zeta function, is at most 2(1 + LY/(2 pi (beta-1))) <= 2 + LY/pi",
    "%d cases, largest sum/bound %s" % (ncase, mp.nstr(worst, 4)))

# N3 Theorem P3, the cancellation: |T_(m,k)(s)| |tau_k|^(1-sigma) -> |Gamma(1-s)| e^(-+ pi t/2), so the terms have exact order |tau_k|^(sigma-1)
ok, rows = True, []
xi, p = mp.mpf(1) / 2, mp.mpf("1.835")
L = mp.log(1 / xi)
sv = mp.mpc("-3.2", "0.8")
sig, tt = mp.re(sv), mp.im(sv)
for m in range(3):
    q = p - m
    for sgn in (1, -1):
        lim = abs(mp.gamma(1 - sv)) * mp.exp(-sgn * mp.pi * tt / 2)
        errs = []
        for kk in (10, 100, 1000, 10000):
            tau = sgn * 2 * mp.pi * kk / L
            av = mp.mpc(q, -tau)
            T = mp.exp(mp.re(mp.loggamma(1 - sv) + mp.loggamma(sv - av) - mp.loggamma(1 - av)))
            errs.append(abs(T * abs(tau) ** (1 - sig) / lim - 1))
        ok &= errs[-1] < mp.mpf("1e-3") and all(errs[i + 1] < errs[i] for i in range(3))
        rows.append(mp.nstr(errs[-1], 2))
rep(ok, "N3 Theorem P3: |T_(m,k)(s)| |tau_k|^(1-sigma) tends to |Gamma(1-s)| e^(-+pi t/2) as k -> +-infinity (xi 1/2, p 1.835, "
        "s -3.2+0.8i, m = 0, 1, 2), the error falling at each tenfold k", "error at k = +-10^4: %s" % ", ".join(rows))

# N4 the whole-shift route of Section 1.4: the step identity on the defining series, and the collapse of the Gamma terms
ok = True
qq = mp.mpf(3) / 7


def fq(sv_, tv_):
    tot = mp.mpc(0)
    for N in range(1, 400):
        tot += qq ** (N * tv_) / ((1 - qq ** N) / (1 - qq)) ** sv_
    return tot


worst_a = mp.mpf(0)
for (sv_, tv_) in [(mp.mpc("1.3", "0.4"), mp.mpc("0.8", "-0.2")), (mp.mpc("-2.1", "1.7"), mp.mpc("1.6", "0.9"))]:
    d = fq(sv_, tv_) - fq(sv_, tv_ + 1) - (1 - qq) * fq(sv_ - 1, tv_)
    worst_a = max(worst_a, abs(d) / abs(fq(sv_, tv_)))
ok &= worst_a < mp.mpf("1e-35")
worst_b = mp.mpf(0)
for (sv_, wv) in [(mp.mpc("-0.7", "0.3"), mp.mpc(0, "4.1")), (mp.mpc("-3.4", "-2.2"), mp.mpc(0, "-9.06")),
                  (mp.mpc("-0.05", "1.9"), mp.mpc(0, "0.77"))]:
    for n in range(1, 6):
        lhs_ = sum(mp.binomial(n, r) * mp.gamma(1 - sv_ + r) * mp.gamma(sv_ - r + wv) for r in range(n + 1)) / mp.gamma(1 + wv)
        rhs_ = mp.gamma(1 - sv_) * mp.gamma(sv_ - n + wv) / mp.gamma(1 - n + wv)
        worst_b = max(worst_b, abs(lhs_ - rhs_) / abs(rhs_))
ok &= worst_b < mp.mpf("1e-35")
rep(ok, "N4 the whole-shift route: f_q(s,t) = f_q(s,t+1) + (1-q) f_q(s-1,t) on the defining series (q 3/7, two points), and "
        "sum_r C(n,r) Gamma(1-s+r) Gamma(s-r+w)/Gamma(1+w) = Gamma(1-s) Gamma(s-n+w)/Gamma(1-n+w) (n = 1 to 5, three points)",
    "worst %s and %s (relative)" % (mp.nstr(worst_a, 2), mp.nstr(worst_b, 2)))

tail = "     %d checks, %.1f s (machine clock %s)" % (len(lines), time.time() - t0, time.strftime("%Y-%m-%d %H:%M:%S"))
print(tail)
lines.append(tail)
lines.append("ALL PASS" if not fails else "FAILED: " + ", ".join(fails))
print(lines[-1])
open(OUT, "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")
