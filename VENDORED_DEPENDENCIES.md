# Vendored Lean sources

The `AlgebraicCombinatorics/` directory contains the following seven source
modules from
[`facebookresearch/algebraic-combinatorics`](https://github.com/facebookresearch/algebraic-combinatorics),
pinned at commit `b6022318e986a0c20764569208ba8ebbe1c04dbf`:

- `QBinomialBasic.lean`
- `Partitions/QBinomialFormulas.lean`
- `SymmetricFunctions/NPartition.lean`
- `SymmetricFunctions/MonomialSymmetric.lean`
- `SymmetricFunctions/LittlewoodRichardson.lean`
- `Determinants/LGVCore.lean` (the checked weighted-LGV core of upstream
  `LGV2.lean`, ending before its unrelated examples and exercise section)
- `SymmetricFunctions/Definitions.lean` (the checked prefix through the
  Newton--Girard identity, ending before unrelated later sections)

Only this transitive closure and the checked LGV prefix are included. In
particular, the upstream `PieriJacobiTrudi.lean` module and the exercise and
native-computation tail of `LGV2.lean` are not present and cannot enter the
proof dependency graph.

The sources are distributed under the license copied to
`ALGEBRAIC_COMBINATORICS_LICENSE`. Small proof-only compatibility changes for
Lean/mathlib `v4.29.0` are applied locally; they do not alter any theorem
statement.
