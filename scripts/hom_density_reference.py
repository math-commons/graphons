#!/usr/bin/env python3
"""Independent brute-force reference for the homomorphism-density differential tests
(EXTENDED_VALIDATION_PLAN.md M1; expected values pinned in Graphons/Tests/Concrete.lean).

t(F, step G) is computed as the average over ALL maps phi : V(F) -> V(G) of
prod_{(a,b) in E(F)} [phi(a) ~ phi(b)], matching the Lean definition
`homDensity_step`. t(F, const p) = p^{e(F)}.

Run: python3 scripts/hom_density_reference.py
"""
from fractions import Fraction
from itertools import product


def t_step(F_edges, F_n, G_adj, G_n):
    """Hom density of F (edge list on range(F_n)) into graph G (adjacency predicate)."""
    total = Fraction(0)
    for phi in product(range(G_n), repeat=F_n):
        if all(G_adj(phi[a], phi[b]) for a, b in F_edges):
            total += 1
    return total / Fraction(G_n) ** F_n


def main():
    K2 = [(0, 1)]
    P3 = [(0, 1), (0, 2)]            # the cherry, centered at 0
    K3 = [(0, 1), (0, 2), (1, 2)]
    C4 = [(0, 1), (1, 2), (2, 3), (3, 0)]

    k4 = lambda a, b: a != b          # K4 on 4 vertices
    c5 = lambda a, b: (a - b) % 5 in (1, 4)   # 5-cycle

    p = Fraction(1, 2)
    checks = [
        ("t(K2, const 1/2)", p ** len(K2), Fraction(1, 2)),
        ("t(P3, const 1/2)", p ** len(P3), Fraction(1, 4)),
        ("t(K3, const 1/2)", p ** len(K3), Fraction(1, 8)),
        ("t(K3, const 9/10)", Fraction(9, 10) ** 3, Fraction(729, 1000)),
        ("t(K2, step K4)", t_step(K2, 2, k4, 4), Fraction(3, 4)),
        ("t(K3, step C5)", t_step(K3, 3, c5, 5), Fraction(0)),
        ("t(P3, step K4)", t_step(P3, 3, k4, 4), Fraction(9, 16)),
        ("t(C4, const 1/2)", Fraction(1, 2) ** len(C4), Fraction(1, 16)),
        ("t(C4, step K4)", t_step(C4, 4, k4, 4), Fraction(21, 64)),
    ]
    ok = True
    for name, got, expected in checks:
        status = "ok" if got == expected else "MISMATCH"
        ok &= got == expected
        print(f"{name:22s} = {str(got):10s} expected {str(expected):10s} [{status}]")

    # Goodman tightness instance used in Concrete.lean: 2p^2 - p <= p^3 at p = 9/10
    p = Fraction(9, 10)
    lhs, rhs = 2 * p**2 - p, p**3
    print(f"goodman @ p=9/10      : {lhs} <= {rhs} [{'ok' if lhs <= rhs else 'MISMATCH'}]")
    ok &= lhs <= rhs

    # Sidorenko-C4 tightness at step K4: t(K2)^4 = (3/4)^4 = 81/256 <= t(C4) = 84/256
    lhs, rhs = t_step(K2, 2, k4, 4) ** 4, t_step(C4, 4, k4, 4)
    print(f"sidorenko_C4 @ step K4: {lhs} <= {rhs} [{'ok' if lhs <= rhs else 'MISMATCH'}]")
    ok &= lhs <= rhs

    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
