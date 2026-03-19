# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

`qsol` is a Lean 4 project containing solutions to exercises from a quantum computing textbook. It uses:
- **Lean 4** (`leanprover/lean4:v4.26.0-rc2`) via `lean-toolchain`
- **Mathlib** for mathematics foundations
- **LeanQuantum** (`quantumlib`) for quantum computing primitives (gates, Pauli operators, Kronecker products)

## Build Commands

```bash
# Build the entire project
lake build

# Update dependencies
lake update

# Check a specific file (useful for checking proofs)
lake build Qsol.chapter_1.solutions
lake build Qsol.chapter_2.solutions
```

## Project Structure

- `lakefile.toml` — Lake build configuration; defines dependencies and Lean options
- `lean-toolchain` — Pins the Lean 4 version
- `Qsol.lean` — Root module; imports `Qsol.Basic` and top-level Quantumlib modules
- `Qsol/Basic.lean` — Minimal shared definitions
- `Qsol/chapter_N/solutions.lean` — Exercise solutions organized by chapter

## Key Lean Options

Set in `lakefile.toml`:
- `relaxedAutoImplicit = false` — all variables must be explicitly declared
- `pp.unicode.fun = true` — use `↦` instead of `=>` in pretty-printing
- `maxSynthPendingDepth = 3`

## Key Imports and Namespaces

Each solutions file typically opens:
```lean
open Kron Matrix Complex
```

Common imports per solutions file:
```lean
import Quantumlib.Data.Basic
import Quantumlib.Tactic.Basic
import Quantumlib.ForMathlib.Data.Matrix.Kron
import Mathlib.LinearAlgebra.Matrix.Kronecker
```

## Quantumlib Types and Tactics

- `CMatrix m n` — complex matrix of dimension `m × n`
- `⊗` — Kronecker product (`kron`)
- `[P| ... ]` — Pauli operator notation
- `solve_matrix` — tactic for discharging concrete matrix equalities (e.g., `!![...] = !![...] ⊗ !![...]`)
- `finProdFinEquiv` — equivalence between `Fin (m * n)` and `Fin m × Fin n`, used to index Kronecker products via `.divNat` / `.modNat`

## Adding New Solutions

1. Create `Qsol/chapter_N/solutions.lean` with the standard imports above
2. Name lemmas/theorems following the pattern `exercise_<chapter>_<section>_<number>` (e.g., `exercise_2_7_1`)
3. Import the new file in `Qsol.lean` if it should be part of the root module
