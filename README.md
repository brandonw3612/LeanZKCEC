# LeanZKCEC

A [Lean](https://lean-lang.org/) formalization of *Proving Circuit Functional Equivalence in Zero Knowledge* by Sirui Shen, Zunchen Huang, and Chenglu Jin (CCS '26, [arXiv:2601.11173](https://arxiv.org/abs/2601.11173)).

The paper proposes *ZK-CEC*, a protocol in which an IP vendor (the prover) convinces a buyer (the verifier) that a secret circuit implementation is functionally equivalent to a public specification, without revealing the implementation. The core idea is to split the miter formula into a public part $\Phi_\text{pub}$ and a secret part $\Phi_\text{sec}$, and to use four sub-protocols $P_1$ – $P_4$ to ensure that proving UNSAT of a partially secret formula remains sound.

The goal of this project is to machine-check that argument, starting from propositional logic and circuit semantics, through the soundness of the blueprint, up to the polynomial encoding and the protocol layer.

## Status

| Module | Content | Status |
| --- | --- | --- |
| `Logic` | Propositional logic, resolution, circuits, Tseitin encoding, miter | Completed |
| `Blueprint` | Lemma 4.1, soundness of secret formula property checking | |
| `Encoding` | Polynomial encoding of clauses and literals, resolution as polynomial constraints, Schwartz–Zippel | |
| `Protocol` | Completeness and soundness of $P_1$ – $P_4$ and $\Pi_\text{ZK-CEC}$ with ideal functionalities | |
| `Crypto` | VOLE IT-MAC binding, PRF assumption | (optional) |
| `Exec` | Executable checker, DIMACS parsing, benchmarks | (optional) |

## Table of Contents

| File | Paper | Content |
| --- | --- | --- |
| [`Basic.lean`](/LeanZKCEC/Logic/Basic.lean) | Sec. 3.1 | Variables, literals, clauses, CNF, assignments, satisfiability |
| [`Vars.lean`](/LeanZKCEC/Logic/Vars.lean) | Sec. 3.1, 4.2 | Variable sets, locality of satisfaction, assignment gluing, projected satisfiability, literal sets as partial assignments, fresh variables |
| [`Resolution.lean`](/LeanZKCEC/Logic/Resolution.lean) | Sec. 3.1, 3.5, Fig. 9 | Resolution with weakening, derivability, index-based refutation proofs and their soundness |
| [`Circuit.lean`](/LeanZKCEC/Logic/Circuit.lean) | Sec. 3.2 | Gate-level netlists (NOT/AND/OR/XOR), evaluation, well-formedness, consistent assignments |
| [`Tseitin.lean`](/LeanZKCEC/Logic/Tseitin.lean) | Sec. 3.2, Fig. 2 | Per-gate Tseitin clauses and the whole-circuit encoding |
| [`Miter.lean`](/LeanZKCEC/Logic/Miter.lean) | Sec. 3.2, Fig. 1 | CNF-level miter, split into $\Phi_\text{pub}$ and $\Phi_\text{sec}$ as in the paper |

## References

- S. Shen, Z. Huang, C. Jin. *Proving Circuit Functional Equivalence in Zero Knowledge*. CCS '26. [arXiv:2601.11173](https://arxiv.org/abs/2601.11173)
- N. Luo, T. Antonopoulos, W. R. Harris, R. Piskac, E. Tromer, X. Wang. *Proving UNSAT in Zero Knowledge*. CCS '22. [doi: 10.1145/3548606.3559373](https://doi.org/10.1145/3548606.3559373)
- The authors' implementation: [NomadShen/ZKCEC](https://github.com/NomadShen/ZKCEC); benchmarks and proof-generation scripts: [NomadShen/CNF-GEN](https://github.com/NomadShen/CNF-GEN)