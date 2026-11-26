# Pair-Sum Periods in Three-Move Subtraction Games

Research manuscript by Haofan Zhang, with Lean proofs and a direct recurrence checker.

- [Manuscript PDF](three-move-subtraction-periods.pdf) and [LaTeX source](main.tex)
- [Lean formalization](anc/SubtractionPeriods.lean) and [verification instructions](anc/README.md)
- [Downloadable manuscript and source archive](https://github.com/Z-bitlance/three-move-subtraction-periods/releases)

The manuscript characterizes when each pair sum is a pure outcome period of a normal-play three-move subtraction game. It gives a reflection proof for Manabe's admissible-angle conjecture and derives the Miklós–Post arithmetic criterion for least pure period `b+c`. Sections 4 and 5 explain how the arguments relate to the earlier results. [Manabe's preprint](https://arxiv.org/abs/2609.05358v2) · [Miklós and Post's paper](https://doi.org/10.1007/s00182-024-00911-5)

## Verify the results

Use Lean 4.19.0 and Python 3. From the repository root, run:

```sh
cd anc
lean --trust=0 -DwarningAsError=true SubtractionPeriods.lean
python3 verify_subtraction_periods.py --max-c 100
```

The Lean file checks both conjectures from the game recurrences. The Python script checks all 161,700 triples with `1 <= a < b < c <= 100`.

The manuscript discloses OpenAI Codex's role in developing the proof strategy and derivations, writing the verification code and Lean formalization, and preparing the text.
