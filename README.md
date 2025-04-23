
# Constant Folding in the While Language (F*)

This project formalizes and verifies **constant folding** as a semantics-preserving optimization for a small While-language, using the [F★ theorem prover](https://www.fstar-lang.org/).

##  Overview

This project demonstrates that **constant folding preserves program semantics**. It encodes a simple imperative While language in [F★](https://www.fstar-lang.org/), a language designed for program verification. It includes:

- An evaluator for expressions and commands.
- A transformation function that performs constant folding.
- A proof that the transformation does not change the semantics of programs.

##  Bounded While Loops

F* requirement that all functions to terminate. Therefore, I modifed the `While` loop construct to take a **user-specified bound** `n : nat`, which is the **maximum number of loop iterations**. This ensures that programs like `while true do skip` (which don't terminate) are excluded.

```fstar
| While : bexp -> command -> nat -> command
```

## Proven Correctness

This repository includes formal F★ proofs of the following two key lemmas:

1. **Expression Folding Preserves Semantics**  
   For any arithmetic expression `e` and state `s`:
   $$
   \texttt{eval\_exp}(s, e) = \texttt{eval\_exp}(s, \texttt{fold\_constants\_exp}(e))
   $$

2. **Constant Folding on Commands Preserves Semantics**  
   For any command `c` and state `s`:
   $$
   \texttt{exec}(s, c) = \texttt{exec}(s, \texttt{const\_fold}(c))
   $$

These are formally proven using F★'s dependent types and lemma constructs.

##  Running Fstar/Checking my proofs

To proof-check the code:

### 1. Download and Install F★

Follow the instructions at the F* install guide [https://www.fstar-lang.org](https://www.fstar-lang.org)

You will also need [Z3](https://github.com/Z3Prover/z3) (version ≥ 4.8.5) in your path.  

Ensure both `fstar.exe` and `z3` are accessible from your terminal.

### 2. Clone and Run

```bash
fstar.exe WhileLang.fst
```

F★ will verify that all the proofs in `WhileLang.fst` succeed, including semantic preservation of constant folding.

##  File Overview

- `WhileLang.fst`: The main file, including the language definition, evaluator, constant folding function, and formal proofs.
- Example test cases demonstrating folding and equality checks for small programs.

## Examples

### Example 1: Arithmetic Folding

```fstar
let test1 = Assign "x" (EAdd (EConst 3) (EConst 4))
let reduced1 = const_fold test1
let expected1 = Assign "x" (EConst 7)
assert (reduced1 == expected1)
```

### Example 2: While Loop

```fstar
let test2 = While (BGt (EVar "x") (EConst 0)) (Assign "x" (ESub (EConst 3) (EConst 1))) 10
let reduced2 = const_fold test2
let expected2 = While (BGt (EVar "x") (EConst 0)) (Assign "x" (EConst 2)) 10
assert (reduced2 == expected2)
```

### Example 3: If Statement

```fstar
let test3 =
  If (BLt (EVar "x") (EConst 10)) (Assign "y" (EAdd (EConst 3) (EConst 2))) (Assign "y" (EConst 2))
let reduced3 = const_fold test3
let expected3 = If (BLt (EVar "x") (EConst 10)) (Assign "y" (EConst 5)) (Assign "y" (EConst 2))
assert (reduced3 == expected3)
```


