# Reproducing the verification

The Lean source uses Lean 4.19.0 and its bundled standard library. From
this directory, run:

```sh
lean --version
lean --trust=0 -DwarningAsError=true SubtractionPeriods.lean
python3 verify_subtraction_periods.py --max-c 100
```

The Lean file derives both conjectures in their original scopes from
the losing-position recurrence and the canonical Sprague–Grundy
function. Sections 4 and 5 of the manuscript explain how the reflection
proof and the arithmetic calculation relate to the earlier criteria
of Miklós–Post and Manabe.

| Manuscript statement | Lean theorem in the SubtractionPeriods namespace |
| --- | --- |
| Section 2, repetition of the initial block | `period_iff_wrap` |
| Section 3, exact candidate-period criteria | `period_short_iff`, `period_middle_iff`, `period_long_iff` |
| Section 3 and Section 5, minimality for c+b | `least_long_iff` |
| Section 4, Manabe's Conjecture 57 | `manabe_conjecture_57_canonical` |
| Section 5, Miklós–Post Conjecture 3 | `miklos_post_conjecture_3_original` |

The last two commands in the Lean source print the axiom dependencies
of the conjecture statements. In both cases Lean reports
`propext`, `Classical.choice`, and `Quot.sound`.

The Python script independently checks the outcome recurrence for
161,700 triples, including additive and nonprimitive move sets.
