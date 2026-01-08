# WP - Weakest Precondition

## Overview

WP (Weakest Precondition) is Frama-C's deductive verification plugin. It uses formal methods to mathematically prove that C programs meet their specifications. WP generates proof obligations from ACSL (ANSI/ISO C Specification Language) annotations and attempts to prove them using automated theorem provers like Alt-Ergo, Z3, CVC4, or Coq.

## Description

The WP plugin implements the weakest precondition calculus, a formal method for program verification. It works backward from postconditions (what should be true after execution) to compute the weakest preconditions (what must be true before execution) that guarantee the postconditions hold.

Key concepts:
- **Proof Obligations**: Logical formulas that must be proven for correctness
- **ACSL Annotations**: Specifications written as comments in the code
- **Automatic Theorem Provers**: External tools that attempt to prove the obligations
- **Memory Models**: Formal models of C memory (Hoare, Typed, Typed+Ref)

## Key Features

- **Mathematical Guarantees**: When a proof succeeds, the property is guaranteed to hold
- **No False Positives**: Proven properties are definitely true
- **Flexible Specifications**: Express complex properties using ACSL
- **Multiple Provers**: Supports various SMT solvers and proof assistants
- **Modular Verification**: Prove functions independently using contracts
- **Memory Models**: Choose between different memory representation strategies

## Pros

✅ **Absolute Certainty**: Successful proofs provide mathematical guarantees
✅ **No False Positives**: Unlike EVA, proven properties are definitely true
✅ **Precise Specifications**: ACSL allows expressing complex requirements
✅ **Compositional**: Verify functions independently with contracts
✅ **Scalable**: Can handle large programs when properly decomposed
✅ **No Test Cases Needed**: Proves properties for all possible inputs
✅ **Documentation**: ACSL specifications serve as formal documentation
✅ **Industry Accepted**: Used in safety-critical and certified systems
✅ **Interactive Proving**: Can use Coq for complex proofs
✅ **Reusable Proofs**: Function contracts enable modular verification

## Cons

❌ **Requires Annotations**: Must write ACSL specifications (time-consuming)
❌ **Expertise Required**: Learning ACSL and proof techniques has a steep curve
❌ **May Not Discharge**: Some true properties may not be automatically proven
❌ **Prover Limitations**: Automated provers have limitations (timeouts, incompleteness)
❌ **Manual Intervention**: Complex proofs may require manual work with Coq
❌ **Not Fully Automatic**: Needs user guidance for specifications
❌ **Pointer Reasoning**: Complex pointer aliasing can be challenging
❌ **Loop Invariants**: Must manually specify what's true at each loop iteration
❌ **Performance**: Proving can be slow for complex properties
❌ **Non-linear Arithmetic**: Limited support for multiplication/division in some provers

## Use Cases

### 1. **Safety-Critical Software Certification**
Meeting certification requirements for:
- Aviation software (DO-178C)
- Medical devices (IEC 62304)
- Automotive systems (ISO 26262)
- Railway systems (EN 50128)

**Why**: Formal proofs provide the highest level of assurance for certification bodies.

### 2. **Cryptographic Algorithm Verification**
Proving correctness of:
- Encryption/decryption implementations
- Hash functions
- Key generation algorithms
- Side-channel resistance properties

**Why**: Mathematical guarantees are essential for security properties.

### 3. **Critical Algorithm Correctness**
Verifying that algorithms work correctly:
- Sorting algorithms
- Search algorithms
- Mathematical computations
- Data structure operations

**Why**: Can prove correctness for all inputs, not just tested cases.

### 4. **Contract-Based Development**
Developing with formal specifications:
- API contract verification
- Component interfaces
- Library functions
- Protocol implementations

**Why**: Contracts serve as executable specifications and enable compositional verification.

### 5. **Memory Safety Proofs**
Proving absence of memory errors:
- No buffer overflows
- No null pointer dereferences
- No use-after-free
- No memory leaks

**Why**: When proofs succeed, these properties are guaranteed for all executions.

### 6. **Functional Correctness**
Proving that functions compute correct results:
- Mathematical functions
- Business logic
- Data transformations
- State machines

**Why**: Goes beyond absence of errors to prove the computation is correct.

### 7. **Invariant Preservation**
Proving that system invariants are maintained:
- Data structure invariants
- Protocol state machines
- Resource management
- Concurrent system properties

**Why**: Ensures critical properties hold throughout execution.

### 8. **Regression Verification**
Ensuring changes don't break proven properties:
- Refactoring with guarantees
- Optimization verification
- Bug fix validation
- Feature addition safety

**Why**: Once proven, properties can be checked automatically on code changes.

## Running WP

### Basic Usage

```bash
# Prove all ACSL annotations in the file
frama-c -wp example.c
```

### With GUI

```bash
frama-c-gui -wp example.c
```

### Common Options

```bash
# Use specific prover (Alt-Ergo, Z3, CVC4, etc.)
frama-c -wp -wp-prover alt-ergo,z3 example.c

# Set timeout for provers (in seconds)
frama-c -wp -wp-timeout 30 example.c

# Generate verbose output
frama-c -wp -wp-verbose 2 example.c

# Focus on specific function
frama-c -wp -wp-fct my_function example.c

# Use specific memory model
frama-c -wp -wp-model Typed+ref example.c

# Generate proof obligations report
frama-c -wp -wp-report example.c

# Try multiple provers in parallel
frama-c -wp -wp-prover alt-ergo,z3,cvc4 -wp-par 4 example.c

# Generate Coq proof scripts for manual proving
frama-c -wp -wp-prover coq -wp-out coq_proofs example.c
```

## Understanding WP Output

WP produces proof statuses for each obligation:

- **✓ Valid**: Proof succeeded - property is guaranteed
- **✗ Unknown**: Prover couldn't decide (timeout or limitation)
- **✗ Failed**: Prover found a counter-example (property is false)

## ACSL Specification Language

### Basic Annotations

```c
/*@ requires x >= 0;          // Precondition: what must be true before
    ensures \result == x * 2;  // Postcondition: what's true after
    assigns \nothing;           // No side effects
*/
int double_value(int x);

/*@ loop invariant 0 <= i <= n;  // What's true at each iteration
    loop assigns i, sum;             // What the loop modifies
    loop variant n - i;              // Termination measure
*/
for (int i = 0; i < n; i++) {
    sum += i;
}

//@ assert x > 0;  // Must be provable at this point
```

### Memory Annotations

```c
/*@ requires \valid(ptr);              // ptr points to valid memory
    requires \valid(arr + (0..n-1));  // array is valid
    ensures \valid(\result);           // returned pointer is valid
*/

/*@ requires \separated(a, b);  // a and b don't overlap */
```

## Example Verification Workflow

1. **Write Code and Specifications**: Add ACSL annotations
2. **Run WP**: `frama-c -wp example.c`
3. **Check Results**: Review which obligations are proven
4. **Strengthen Specs**: Add missing preconditions or loop invariants
5. **Try Different Provers**: Some provers work better for certain problems
6. **Increase Timeout**: Give provers more time
7. **Simplify**: Break complex proofs into smaller lemmas
8. **Manual Proof**: Use Coq for obligations that can't be automatically proven

## Tips for Better Results

1. **Start Simple**: Begin with basic properties, add complexity gradually
2. **Strong Preconditions**: Specify all assumptions about inputs
3. **Loop Invariants**: Critical for proving loops - state what's preserved
4. **Loop Variants**: Prove termination with decreasing measure
5. **Assertions**: Add intermediate assertions to guide provers
6. **Lemmas**: Factor out complex reasoning into proven lemmas
7. **Multiple Provers**: Different provers have different strengths
8. **Memory Model**: Choose appropriate model (Typed+ref often best)
9. **Modular Verification**: Use function contracts to avoid re-proving
10. **Read Counter-examples**: When proofs fail, understand why

## Memory Models

WP supports different memory models:

- **Hoare**: Simple model, limited pointer reasoning
- **Typed**: Type-based separation, good for most programs
- **Typed+ref**: Adds region analysis, best for complex pointer usage

Choose based on your code's complexity and pointer usage.

## Integration with Other Analyzers

- **EVA**: Run EVA first to get value ranges, helps WP proofs
- **RTE**: Generate runtime error annotations, then prove them with WP
- **Slicing**: Reduce code to relevant parts before proving

## Supported Provers

- **Alt-Ergo**: Default, good general-purpose prover
- **Z3**: Microsoft's SMT solver, very powerful
- **CVC4/CVC5**: Good for quantifiers and arrays
- **Coq**: Interactive proof assistant for complex proofs
- **Vampire**: Automated theorem prover
- **E-Prover**: Superposition-based prover

## Further Reading

- [WP Plugin Manual](https://frama-c.com/html/wp-manual/index.html)
- [ACSL Specification](https://frama-c.com/html/acsl.html)
- [Deductive Verification Tutorial](https://frama-c.com/html/tutorial-deductive-verification.html)
- [WP Examples](https://frama-c.com/html/wp-examples.html)
