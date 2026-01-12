# EVA - Evolved Value Analysis

## Overview

EVA (Evolved Value Analysis) is one of the most powerful and widely-used analyzers in Frama-C. It performs abstract interpretation to compute an over-approximation of all possible values that program variables can take during execution. EVA can detect potential runtime errors, undefined behaviors, and provide insights into program behavior without executing the code.

## Description

EVA analyzes C programs by computing abstract values for all variables at each program point. It tracks:
- Numerical values and ranges
- Pointer values and memory states
- Array indices and buffer boundaries
- Possible function call targets
- Uninitialized variables

The analyzer uses sophisticated abstract domains to represent sets of possible values efficiently. It can handle complex C constructs including pointers, dynamic memory, function pointers, and recursive functions.

## Key Features

- **Sound Analysis**: EVA guarantees to detect all potential runtime errors (if it says the code is safe, it is safe)
- **Abstract Interpretation**: Uses mathematical techniques to reason about all possible executions
- **Automatic**: Requires minimal or no annotations for basic analysis
- **Compositional**: Can analyze functions independently and combine results
- **Configurable Precision**: Multiple abstract domains can be enabled for different precision/performance trade-offs

## Pros

✅ **Automatic Analysis**: Works out-of-the-box with minimal user intervention
✅ **No False Negatives**: Sound analysis means all real errors will be detected
✅ **Handles Complex Code**: Can analyze pointer arithmetic, arrays, structures, unions
✅ **Fast for Many Programs**: Efficient algorithms for common code patterns
✅ **Comprehensive Coverage**: Analyzes the entire program, not just annotated parts
✅ **Good for Legacy Code**: Doesn't require specifications or modifications to existing code
✅ **Memory Safety**: Excellent at detecting buffer overflows, null pointer dereferences, use-after-free
✅ **Incremental Analysis**: Can focus on specific parts of the code

## Cons

❌ **Over-approximation**: May report false positives (alarms that aren't real errors)
❌ **Precision Limitations**: Abstract domains may lose precision with complex computations
❌ **Scalability**: Can be slow or imprecise on very large programs
❌ **Loop Handling**: May need manual loop unrolling hints for better precision
❌ **Non-linear Arithmetic**: Limited precision with multiplication and division
❌ **Floating-point**: Limited precision for floating-point computations
❌ **Learning Curve**: Understanding alarm messages and improving precision requires experience
❌ **Memory Usage**: Can consume significant memory on large codebases

## Use Cases

### 1. **Security-Critical Code Analysis**
EVA is ideal for analyzing security-sensitive code like:
- Cryptographic implementations
- Network protocol parsers
- Input validation routines
- Authentication systems

**Why**: Automatically detects buffer overflows, integer overflows, and other memory safety issues.

### 2. **Legacy Code Verification**
When working with old C codebases without specifications:
- Understanding program behavior
- Finding hidden bugs
- Preparing for refactoring
- Creating test cases

**Why**: Requires no code modification or annotations to get started.

### 3. **Embedded Systems**
Analyzing embedded software and firmware:
- Device drivers
- Real-time systems
- Low-level hardware interaction code
- Resource-constrained applications

**Why**: Can analyze code that's difficult to test in real environments.

### 4. **Buffer Overflow Detection**
Finding memory safety violations:
- Array bounds violations
- Pointer arithmetic errors
- Stack and heap buffer overflows
- String manipulation bugs

**Why**: EVA excels at tracking memory states and pointer values.

### 5. **Initial Code Review**
First-pass analysis before deeper verification:
- Quick overview of potential issues
- Identifying areas that need attention
- Prioritizing code for manual review or formal verification

**Why**: Fast automated analysis provides good coverage.

### 6. **Undefined Behavior Detection**
Finding C undefined behaviors:
- Uninitialized variable use
- Integer overflow
- Division by zero
- Invalid pointer operations
- Signed integer overflow

**Why**: Comprehensive tracking of all program states.

## Running EVA

### Basic Usage

```bash
frama-c -eva example.c
```

### With GUI

```bash
frama-c-gui -eva example.c
```

### Common Options

```bash
# Increase precision with specific abstract domains
frama-c -eva -eva-precision 5 example.c

# Focus on specific function
frama-c -eva -main my_function example.c

# Generate value analysis report
frama-c -eva -eva-show-progress example.c

# With more verbose output
frama-c -eva -eva-verbose 2 example.c

# Unroll loops for better precision
frama-c -eva -eva-min-loop-unroll 10 example.c
```

## Understanding EVA Output

EVA produces several types of messages:

- **🟢 Green (Valid)**: Property is guaranteed to hold
- **🟡 Orange (Unknown)**: EVA cannot determine if property holds (alarm)
- **🔴 Red (Invalid)**: Property is guaranteed to be violated

Alarms indicate potential issues that may be false positives or require more precise analysis.

## Example Analysis Workflow

1. **Run basic EVA analysis**: `frama-c -eva example.c`
2. **Review alarms**: Check which properties are unknown
3. **Add ACSL annotations**: Provide preconditions to improve precision
4. **Adjust parameters**: Use `-eva-precision` or domain options
5. **Iterate**: Refine analysis until acceptable precision

## Tips for Better Results

1. **Provide Entry Point Context**: Use `-eva-main` and add preconditions for input values
2. **Add Loop Invariants**: Help EVA understand loop behavior
3. **Limit Input Ranges**: Specify realistic bounds for variables
4. **Use Assertions**: Add checks to split analysis paths
5. **Increase Unrolling**: For small loops, unrolling can improve precision
6. **Enable Specific Domains**: Activate domain-specific abstract interpretations

## Integration with Other Analyzers

EVA works well with:
- **RTE**: Generate runtime error annotations first, then analyze with EVA
- **WP**: Use EVA results to guide proof attempts
- **Slicing**: Focus EVA on sliced code for better performance

## Further Reading

- [EVA Plugin Documentation](https://frama-c.com/html/eva-manual/index.html)
- [Abstract Interpretation Tutorial](https://frama-c.com/html/tutorial-abstract-interpretation.html)
- [Value Analysis Options](https://frama-c.com/html/eva-options.html)
