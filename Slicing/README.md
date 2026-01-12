# Slicing - Program Slicing

## Overview

Slicing is a Frama-C plugin that performs program slicing, a technique for extracting the parts of a program that potentially affect the values computed at specific program points. It helps understand complex programs by reducing them to only the code that matters for a particular criterion (variable, statement, or property).

## Description

Program slicing identifies and extracts a subset of program statements that may affect the value of a variable at a specific point (the slicing criterion). The resulting "slice" is a smaller, simpler program that preserves the behavior relevant to that criterion.

Types of slicing:
- **Backward Slicing**: What affects a given point (most common)
- **Forward Slicing**: What is affected by a given point
- **Static Slicing**: Considers all possible executions
- **Dynamic Slicing**: Based on specific execution traces

Frama-C's slicing plugin primarily performs backward static slicing.

## Key Features

- **Dependency Analysis**: Tracks both control and data dependencies
- **Inter-procedural**: Handles function calls across the program
- **Precise**: Uses sophisticated pointer and aliasing analysis
- **Customizable Criteria**: Slice on variables, statements, or assertions
- **Code Simplification**: Removes irrelevant code automatically
- **Export**: Can export sliced code as standalone C program

## Pros

✅ **Program Understanding**: Simplifies complex code to essential parts
✅ **Debugging Aid**: Focuses on code relevant to a bug
✅ **Testing**: Reduces code to test for specific properties
✅ **Maintenance**: Identifies code dependencies before changes
✅ **Verification**: Reduces verification effort by eliminating irrelevant code
✅ **Code Review**: Focus review on relevant sections
✅ **Automatic**: No annotations required
✅ **Precise**: Sound analysis of dependencies
✅ **Documentation**: Shows what influences a computation
✅ **Impact Analysis**: Understand effects of changes

## Cons

❌ **Can Be Large**: Slices may still be substantial for complex dependencies
❌ **Requires Criterion**: Must specify what to slice on
❌ **Learning Curve**: Understanding dependency analysis takes time
❌ **Not Always Minimal**: May include more code than strictly necessary
❌ **Pointer Complexity**: Complex pointer aliasing can reduce precision
❌ **Scalability**: Very large programs can slow down analysis
❌ **Context Loss**: Removed code may affect understanding

## Use Cases

### 1. **Program Comprehension**
Understanding complex legacy code:
- Identify what affects specific variables
- Understand computation chains
- Trace data flow through functions
- Simplify tangled code

**Why**: Reduces cognitive load by showing only relevant code.

### 2. **Debugging**
Focusing debugging efforts:
- Find all code that could cause a bug
- Eliminate irrelevant code from consideration
- Trace error propagation
- Identify root causes

**Why**: Narrows down where to look for problems.

### 3. **Security Analysis**
Analyzing security-critical operations:
- Trace input validation paths
- Identify what affects security checks
- Analyze authentication flows
- Track sensitive data flow

**Why**: Ensures all relevant security code is examined.

### 4. **Code Review**
Focused code reviews:
- Review only code affecting critical properties
- Understand change impact
- Verify security-sensitive operations
- Validate input handling

**Why**: Makes reviews more efficient and thorough.

### 5. **Testing**
Targeted test generation:
- Identify code needing tests for specific properties
- Reduce code under test
- Focus test cases
- Improve test coverage strategies

**Why**: Helps prioritize testing efforts.

### 6. **Impact Analysis**
Understanding change effects:
- See what depends on code to be modified
- Assess refactoring risks
- Plan incremental changes
- Validate change scope

**Why**: Prevents unintended side effects.

### 7. **Verification Preparation**
Before formal verification:
- Reduce code for EVA or WP
- Focus verification on relevant parts
- Improve analyzer performance
- Simplify proof obligations

**Why**: Makes verification faster and more tractable.

### 8. **Feature Extraction**
Extracting specific functionality:
- Extract one feature from multi-feature code
- Create focused examples
- Understand feature interactions
- Prepare for modularization

**Why**: Isolates specific functionality.

### 9. **Dead Code Detection**
Finding unused code:
- Identify code not in any slice
- Find unreachable code
- Clean up codebases
- Optimize programs

**Why**: Code not in any slice may be dead code.

### 10. **Regression Testing**
Focused regression tests:
- Identify what changes could affect
- Prioritize regression tests
- Understand test dependencies
- Optimize test suites

**Why**: Run only tests affected by changes.

## Running Slicing

### Basic Usage

```bash
# Slice on return value of main function
frama-c -slice-return main example.c
```

### With GUI

```bash
frama-c-gui -slice-return main example.c
```

### Common Options

```bash
# Slice on specific function's return value
frama-c -slice-return function_name example.c

# Slice on a specific variable at a function call
frama-c -slice-calls function_name example.c

# Print the sliced code
frama-c example.c -slice-return main -then-on 'Slicing export' -print

# Export sliced code to file
frama-c example.c -slice-return main -then-on 'Slicing export' -print -ocode sliced.c

# Multiple slicing criteria
frama-c -slice-return main -slice-return other_func example.c

```

## Slicing Criteria

### 1. Function Return Value

```bash
frama-c -slice-return function_name example.c
```
Extracts code affecting the return value of specified function.

### 2. Function Calls

```bash
frama-c -slice-calls function_name example.c
```
Includes all code affecting calls to the function.

### 3. Specific Variable

```bash
# Add pragma in source code:
//@ slice pragma expr my_variable;
frama-c -slice-pragma my_variable example.c
```

### 4. Assertions

```bash
frama-c -slice-assert function_name example.c
```
Slices on all assertions in the function.

## Understanding Slicing Output

The slicing plugin produces:
1. **Dependency Graph**: Shows relationships between code elements
2. **Sliced Code**: The extracted program subset
3. **Statistics**: Information about reduction achieved

Sliced code includes:
- All statements that directly affect the criterion
- All statements with data dependencies
- All control flow affecting the criterion
- All necessary declarations and definitions

## Example Workflow

1. **Identify Criterion**: Choose what to slice on (e.g., return value)
2. **Run Slicing**: `frama-c -slice-return main example.c`
3. **Review Results**: Examine slicing statistics
4. **Export Slice**: `frama-c -slice-return main -then-on 'Slicing export' -print -ocode sliced.c example.c`
5. **Analyze Slice**: Study the reduced code
6. **Iterate**: Try different criteria if needed

## Using Slicing with Other Analyzers

### Before EVA
```bash
# Slice then analyze with EVA
frama-c -slice-return main -then-on 'Slicing export' -eva example.c
```
Reduces code before value analysis for better performance.

### Before WP
```bash
# Slice then verify with WP
frama-c -slice-return main -then-on 'Slicing export' -wp example.c
```
Focus formal verification on relevant code.

### After RTE
```bash
# Generate annotations then slice
frama-c -rte -then -slice-return main example.c
```
Combine runtime error detection with slicing.

## Slicing Pragmas

Insert slicing criteria directly in source code:

```c
//@ slice pragma expr variable_name;
```

This marks a program point to slice on.

Example:
```c
int compute(int x) {
    int result = x * 2;
    //@ slice pragma expr result;
    return result;
}
```

Then slice with:
```bash
frama-c -slice-pragma result example.c
```

## Advanced Features

### Persistent Slicing Selection

Build complex slicing criteria interactively in GUI:
1. Select multiple criteria
2. Compute union or intersection of slices
3. Manually add/remove statements
4. Export final result

### Spare Code

Code not in the slice is "spare code" - potentially:
- Dead code
- Code for other features
- Error handling for different paths
- Unreachable code

## Tips for Effective Slicing

1. **Choose Good Criteria**: Pick meaningful slicing points
2. **Start Specific**: Begin with focused criteria
3. **Understand Dependencies**: Study what's included and why
4. **Iterate**: Try different criteria to understand the code
5. **Combine Analyses**: Use with EVA/WP for better results
6. **Document**: Note why certain code is in the slice
7. **Review Spare Code**: Understand what's excluded
8. **Use GUI**: Interactive exploration helps understanding

## Interpretation Tips

When analyzing slices:
- **All included code matters**: Every statement affects the criterion
- **Removed code**: Doesn't affect the specific criterion (but may affect other properties)
- **Control dependencies**: Code controlling execution paths is included
- **Data dependencies**: Code producing used values is included
- **Conservative**: May include code that doesn't always affect the criterion

## Performance Considerations

- Slicing is generally fast for medium-sized programs
- Very large programs may take longer
- Complex pointer aliasing increases computation time
- Multiple criteria are processed efficiently
- GUI is helpful for large slices

## Common Patterns

### Pattern 1: Bug Localization
```bash
# Slice on suspicious variable
frama-c -slice-return buggy_function example.c
```

### Pattern 2: Feature Understanding
```bash
# Slice on feature output
frama-c -slice-return feature_compute example.c
```

### Pattern 3: Security Analysis
```bash
# Slice on security check
frama-c -slice-calls security_validate example.c
```

## Limitations

- **Soundness**: May include unnecessary code (conservative)
- **Not Minimization**: Doesn't guarantee smallest possible slice
- **Pointer Precision**: Complex aliasing may reduce precision
- **Criteria Needed**: Requires knowing what to slice on
- **Context**: Removed code may affect program understanding

## Further Reading

- [Slicing Plugin Documentation](https://frama-c.com/html/slicing-manual/index.html)
- [Program Slicing Overview](https://frama-c.com/html/program-slicing.html)
- [Slicing Tutorial](https://frama-c.com/html/tutorial-slicing.html)
