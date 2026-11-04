#!/usr/bin/env python3
"""Rational intervals for the certificate Table1Cert (Table 1 of the paper, n = 1..20).

Reads run.jsonl, the certified records of 02_certify.py (Zenodo 10.5281/zenodo.23269807):
exact sums S(N_n), S(N_n^-), computed with primesum and checked by a second algorithm.
For each n, with Arb (python-flint, 400 bits):
  * gamma_n = acb.zeta_zero(n).imag, a rigorous ball with certified isolation;
  * lo < gamma_n < hi, rationals with denominator 10^24;
  * log S(N_n^-) < lo and hi <= log S(N_n), with S(N_n) - S(N_n^-) = N_n.
Where a sieve is practical (N_n <= 10^8) the sums are recomputed.

Usage: certify_table1.py run.jsonl table1_cert.txt
Output lines: n lo_numerator hi_numerator N_n N_n^- S(N_n) S(N_n^-)   (denominator 10^24)
"""
import json, sys
import numpy as np
import flint
from flint import arb, acb

flint.ctx.prec = 400
DEN = 10 ** 24


def sieve_sum(limit, xs):
    s = np.ones(limit + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(limit ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    p = np.nonzero(s)[0]
    return {x: 1 + int(p[p <= x].astype(np.int64).sum()) for x in xs}


def main():
    recs = [json.loads(line) for line in open(sys.argv[1])]
    assert [r["n"] for r in recs] == list(range(1, 21)) and all(r["certified"] for r in recs)
    small = [x for r in recs if r["N"] <= 10 ** 8 for x in (r["N"], r["N_prev"])]
    check = sieve_sum(max(small), small)
    with open(sys.argv[2], "w") as out:
        for r in recs:
            n, N, Np, SN, Sp = r["n"], r["N"], r["N_prev"], int(r["S_N"]), int(r["S_prev"])
            if N <= 10 ** 8:
                assert check[N] == SN and check[Np] == Sp
            assert SN - Sp == N
            g = acb.zeta_zero(n).imag
            mid = int((g * DEN).floor().unique_fmpz())
            lo, hi = mid - 1, mid + 2
            alo, ahi = arb(lo) / DEN, arb(hi) / DEN
            assert bool(alo < g) and bool(g < ahi)
            assert bool(arb(Sp).log() < alo) and bool(ahi <= arb(SN).log())
            out.write(f"{n} {lo} {hi} {N} {Np} {SN} {Sp}\n")
            print(n, "ok", float(arb(SN).log() - ahi), float(alo - arb(Sp).log()))


main()
