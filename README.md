# JSP-000452 · Size Ramsey numbers of two star forests

This Lean 4 project proves the full Erdős problem 561 identity. For every pair of nonempty, nonincreasing lists of positive star sizes, the two-colour size Ramsey number is the sum of the maxima on the antidiagonals indexed from 2 through the sum of the list lengths.

The mathematical solution is by **Peilin Liu (P. Liu)**. Theorem 1.1, page 3, in *Size Ramsey Numbers of Arbitrary Star Forests*, version 3, November 2, 2026, gives the full formula. The publication and mathematical submission are linked separately. [Zenodo v3](https://doi.org/10.5281/zenodo.23879458) · [Liu’s submission](https://github.com/TheJustinSunPrize/awards/pull/5518)

The **Lean formalization** was developed in the shuaoo-create project with OpenAI Codex assistance. The final argument uses one weighted deletion on the whole positive core and applies its bound to the same exterior stage and the same smaller forcing row. The proof covers every allowed degree and both parities.

## Theorem and reference

The complete declaration is `JSP452Audit.StarHost.erdos_561`. Its type reproduces the pinned reference quantifiers, star notation, host edge count and one-based antidiagonal convention. The two assignments in the verification entry check the reference and project formulations. [Final theorem](Proof/JSP452OfficialProof.lean) · [Verification entry](Proof/JSP452.lean) · [Pinned upstream specification](https://github.com/google-deepmind/formal-conjectures/blob/2783e6edc3b2c80b5844978f74c3b325df8d82f5/FormalConjectures/ErdosProblems/561.lean)

## Reproduce

Check out the full commit SHA cited in the catalog submission. From the repository root, with Git and elan available, run the following commands.

```sh
lean --version
lake exe cache get
lake build JSP452
lake env lean -R Proof Proof/JSP452.lean
```

The pinned compiler is Lean 4.33.1 and the mathlib commit is `0df444a360eaa60ab8c11dca51a86af692955474`. The verification entry prints the terminal axiom dependencies `propext`, `Classical.choice` and `Quot.sound`. [Toolchain](lean-toolchain) · [Dependency manifest](lake-manifest.json) · [Formalization metadata](formalization.yaml)

The reference statement and SizeRamsey definition carry the Formal Conjectures authors’ Apache 2.0 notices. The mathematical manuscript and its original source are distributed by P. Liu under CC BY 4.0. [Upstream license](licenses/Apache-2.0.txt) · [Mathematical source](solution/README.md)
