#!/usr/bin/env python3
"""Check the paper's tests against the normal-play outcome recurrence."""

import argparse
from itertools import combinations


def outcomes(a, b, c, stop):
    losing = bytearray(stop)
    for n in range(stop):
        losing[n] = not (
            (n >= a and losing[n - a])
            or (n >= b and losing[n - b])
            or (n >= c and losing[n - c])
        )
    return losing


def check(a, b, c):
    modulus = a + b
    rho = c % modulus
    delta = b - a
    zero_residues = {u for u in range(b) if u // a % 2 == 0}
    gaps = set(range(a, b)) - zero_residues
    terminal_gaps = set(range(delta, b)) - zero_residues
    translated_gaps = {(rho + u) % modulus for u in terminal_gaps}

    short = not any((rho + z) % modulus in zero_residues for z in zero_residues)
    middle = not any(
        (rho + z - delta) % modulus in zero_residues
        for z in zero_residues
        if z < delta
    )
    long = all((u + a) % modulus in zero_residues for u in translated_gaps)
    admissible = translated_gaps.isdisjoint(zero_residues) and all(
        (rho + u) % modulus not in terminal_gaps for u in gaps
    )

    longest_candidate = c + b
    losing = outcomes(a, b, c, c + longest_candidate)
    prefix = losing[:c]

    # Once the first c positions agree after a shift, the recurrence
    # gives agreement at every later position by induction.
    for period, predicted in ((modulus, short), (c + a, middle), (c + b, long)):
        actual = prefix == losing[period : period + c]
        if actual != predicted:
            raise AssertionError((a, b, c, period, predicted, actual))
    if admissible != long:
        raise AssertionError((a, b, c, "admissibility", admissible, long))

    q, r = divmod(b, a)
    j, t = divmod(rho, 2 * a)
    sigma = (c - a) % modulus
    j_prime, t_prime = divmod(sigma, 2 * a)
    if q % 2 == 0:
        arithmetic = (
            sigma > 0
            and t_prime <= r
            and 2 * j_prime <= q
            and (2 * j_prime < q or t_prime <= 2 * r - a)
        )
    elif r:
        arithmetic = r <= t <= a and (j > 0 or t < a)
    else:
        arithmetic = t != a

    actual_least = prefix == losing[longest_candidate : longest_candidate + c]
    if actual_least:
        block = losing[:longest_candidate]
        actual_least = not any(
            block == block[:d] * (longest_candidate // d)
            for d in range(1, longest_candidate // 2 + 1)
            if longest_candidate % d == 0
        )
    if actual_least != arithmetic:
        raise AssertionError((a, b, c, "least period c+b", arithmetic, actual_least))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-c", type=int, default=100)
    args = parser.parse_args()
    if args.max_c < 3:
        parser.error("--max-c must be at least 3")
    count = 0
    for a, b, c in combinations(range(1, args.max_c + 1), 3):
        check(a, b, c)
        count += 1
    print(
        f"Verified {count:,} triples with 1 <= a < b < c <= {args.max_c}. "
        "All three period tests, the admissibility equivalence, and the "
        "arithmetic test for least period c+b agree."
    )


if __name__ == "__main__":
    main()
