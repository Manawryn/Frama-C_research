# WP - Weakest Precondition

## Overview

WP (Weakest Precondition) is Frama-C's deductive verification plugin. It uses formal methods to mathematically prove that C programs meet their specifications. WP generates proof obligations from ACSL (ANSI/ISO C Specification Language) annotations and attempts to prove them using automated theorem provers like Alt-Ergo, Z3, CVC4, or Coq.

## Description

The WP plugin implements the weakest precondition calculus, a formal method for program verification. It works backward from postconditions (what should be true after execution) to compute the weakest preconditions (what must be true before execution) that guarantee the postconditions hold.

Key concepts in the provided `example.c`:
- **Contracts**: Function preconditions (`requires`) and postconditions (`ensures`)
- **Loop Invariants**: Properties that remain true throughout loop iterations
- **Loop Variants**: Terms that decrease to prove termination
- **Quantification**: Using `\forall` to describe array properties
- **Labels**: Using `\at(..., Pre)` to refer to initial states inside loops

## Key Features

- **Mathematical Guarantees**: When a proof succeeds, the property is guaranteed to hold
- **No False Positives**: Proven properties are definitely true
- **Flexible Specifications**: Express complex properties using ACSL
- **Multiple Provers**: Supports various SMT solvers and proof assistants
- **Modular Verification**: Prove functions independently using contracts

## Pros

✅ **Absolute Certainty**: Successful proofs provide mathematical guarantees
✅ **No False Positives**: Unlike EVA, proven properties are definitely true
✅ **Precise Specifications**: ACSL allows expressing complex requirements
✅ **Compositional**: Verify functions independently with contracts
✅ **Scalable**: Can handle large programs when properly decomposed
✅ **No Test Cases Needed**: Proves properties for all possible inputs
✅ **Industry Accepted**: Used in safety-critical and certified systems

## Cons

❌ **Requires Annotations**: Must write ACSL specifications (time-consuming)
❌ **Expertise Required**: Learning ACSL and proof techniques has a steep curve
❌ **Manual Intervention**: Complex proofs may require manual work with Coq
❌ **Loop Invariants**: Must manually specify what's true at each loop iteration
❌ **Performance**: Proving can be slow for complex properties

## Use Cases

### 1. **Safety-Critical Software Certification**
Meeting certification requirements for:
- Aviation software (DO-178C)
- Medical devices (IEC 62304)
- Automotive systems (ISO 26262)

### 2. **Critical Algorithm Correctness**
Verifying that algorithms work correctly:
- Sorting algorithms (see `is_sorted` in example)
- Search algorithms (see `linear_search` in example)
- Mathematical computations (see `factorial` in example)

### 3. **Memory Safety Proofs**
Proving absence of memory errors:
- No buffer overflows
- No null pointer dereferences (see `swap` and `array_init`)
- Valid memory access

## Running the Example
```bash
# Basic verification using default settings
frama-c -wp example.c

# Use specific provers (Z3 is recommended for factorial/math)
frama-c -wp -wp-prover alt-ergo,z3 example.c

# Increase timeout to 60s for complex loops
frama-c -wp -wp-timeout 60 example.c

# Split complex goals into smaller parts (helps is_sorted)
frama-c -wp -wp-split example.c

# Generate and prove Runtime Error checks (overflows, valid pointers)
frama-c -wp -wp-rte example.c

# Run with GUI to visually inspect why a goal failed
frama-c-gui -wp example.c

# Focus verification on a single function only
frama-c -wp -wp-fct array_reverse example.c

# Print the mathematical proof obligations to terminal
frama-c -wp -wp-print example.c

# Generate a verification report file
frama-c -wp -wp-report report.json example.c

# specific command to likely solve your current timeouts
frama-c -wp -wp-prover alt-ergo,z3 -wp-timeout 60 -wp-split example.c
```

### Prerequisites

Ensure you have a prover installed and detected:
```bash
# 1. Install Alt-Ergo (if using opam)
opam install alt-ergo

# 2. Detect provers
why3 config --detect