"""D1 near p = 1/2: the Thue-Morse Dirichlet series.

The first-order perturbation beta_n of strategy ALL at p = 1/2 has
profile Phi^B with Fourier coefficients

    hat-Phi^B(m) = (1/log2) * M[Lambda](s_m),     s_m = 2 pi i m / log2,

    M[Lambda](s) = int_0^inf e^{-w/2} F(w) w^s dw,
    F(w) = prod_{j>=0} (1 - e^{-2^j w}) = sum_n (-1)^{s_2(n)} e^{-n w}.

Closed form: M[Lambda](s) = Gamma(s+1) T(s+1), T(sigma) = sum t_n
(n+1/2)^{-sigma}, and T(sigma) = -(2^sigma - 1) D(sigma) with D the
Thue-Morse Dirichlet series D(sigma) = sum_{m>=1} (-1)^{s_2(m)}
m^{-sigma}.  At sigma = 1 + s_m one has 2^sigma = 2, so

    T(1+s_m) = -D(1+s_m),     hat-Phi^B(m) = -(1/log2) Gamma(1+s_m) D(1+s_m).

D1 near p = 1/2  <=>  D(1+s_m) != 0 for some m != 0.

This script evaluates D(1+s_m) = -M[Lambda](s_m)/Gamma(1+s_m) for
m = 0,1,2,3, confirming D(1+s_1) != 0 and of size O(1).

Run from the repository root:
    .venv/bin/python simulation/d1_thue_morse.py
"""

from mpmath import mp, mpf, mpc, pi, log, gamma, quad, exp, inf

mp.dps = 30
L = log(2)


def F(w):
    """F(w) = prod_{j>=0} (1 - e^{-2^j w})."""
    prod = mpf(1)
    a = w
    while a < 60:                      # factors with 2^j w >= 60 are ~1
        prod *= (1 - exp(-a))
        a *= 2
    return prod


def mellin_Lambda(s):
    """M[Lambda](s) = int_0^inf e^{-w/2} F(w) w^s dw  (a clean bump)."""
    return quad(lambda w: exp(-w / 2) * F(w) * w**s,
                [0, mpf(1), 5, 20, inf])


def main():
    print(f"L = log 2 = {float(L):.8f}")
    print(f"s_1 = 2 pi i / L = {complex(2j * pi / L):.6f}\n")
    print(f"{'m':>2}  {'D(1+s_m)':>30}  {'|D(1+s_m)|':>12}  "
          f"{'hat-Phi^B(m)':>26}")
    print("-" * 78)
    for m in (0, 1, 2, 3):
        s_m = 2j * pi * m / L
        ML = mellin_Lambda(s_m)
        Phi_hat = ML / L
        D_val = -ML / gamma(1 + s_m)
        print(f"{m:>2}  {complex(D_val):>30.10f}  "
              f"{float(abs(D_val)):>12.8f}  {complex(Phi_hat):>26.4e}")
    print()
    print(" m=0 row: D(1) and the mean hat-Phi^B(0) = mean of beta_n")
    print("          (cross-check: should be ~ 1.726).")
    print(" m=1 row: |D(1+s_1)| is O(1) and non-zero  =>  Phi_p is")
    print("          non-constant near p=1/2  =>  D1 holds there.")
    print(" The smallness of hat-Phi^B(1) ~ 1e-5 is entirely the")
    print(" Gamma(1+s_1) ~ 1e-6 damping; D(1+s_1) itself is O(1).")


if __name__ == "__main__":
    main()
