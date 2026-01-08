# RTE - Runtime Error Annotation Generator

## Overview

RTE (Runtime Error) is a Frama-C plugin that automatically generates ACSL annotations for potential runtime errors in C programs. It acts as a bridge between automated analysis (like EVA) and formal verification (like WP), by making implicit safety conditions explicit through annotations. RTE doesn't verify the code itself but generates assertions that can be checked by other analyzers.

## Description

The RTE plugin inserts ACSL assertions at every program point where a runtime error could potentially occur according to the C standard. These annotations make the implicit safety requirements of C operations explicit, allowing other plugins to verify them.

Types of runtime errors detected:
- **Division by zero**
- **Integer overflow/underflow**
- **Invalid pointer dereferences**
- **Array out-of-bounds accesses**
- **Invalid shifts**
- **Invalid memory accesses**
- **Uninitialized variable usage**
- **Invalid downcasts**

## Key Features

- **Automatic Generation**: No manual annotation required
- **Comprehensive Coverage**: Checks all potential runtime errors per C standard
- **Plugin Integration**: Works seamlessly with EVA and WP
- **Selective Generation**: Can target specific error types
- **ACSL Output**: Generates standard ACSL assertions
- **Preprocessing Step**: Typically run before other analyzers

## Pros

✅ **Fully Automatic**: Requires no user input or annotations
✅ **Comprehensive**: Covers all C undefined behaviors
✅ **Fast**: Quick annotation generation
✅ **Integration**: Perfect bridge between EVA and WP
✅ **Explicit Safety**: Makes implicit safety conditions visible
✅ **Selective**: Can choose which error types to annotate
✅ **Standard Compliance**: Based on C standard undefined behaviors
✅ **Documentation**: Annotations serve as safety documentation
✅ **Educational**: Helps understand C's runtime error conditions

## Cons

❌ **No Verification**: Only generates annotations, doesn't prove them
❌ **Requires Other Tools**: Must use EVA or WP to check the annotations
❌ **Can Be Verbose**: Generates many annotations for complex code
❌ **Not Context-Aware**: May generate annotations for impossible errors
❌ **Limited to C Standard**: Only covers standard-defined undefined behaviors
❌ **Platform-Specific**: Some behaviors depend on implementation

## Use Cases

### 1. **Preparing Code for Formal Verification**
Before using WP for deductive verification:
- Generate all safety annotations automatically
- Create proof obligations for runtime safety
- Identify what needs to be proven
- Establish verification baseline

**Why**: Saves time manually writing safety assertions.

### 2. **Combining with EVA Analysis**
Using RTE with EVA for comprehensive safety analysis:
1. Run RTE to generate assertions
2. Run EVA to check the assertions
3. Review which assertions cannot be proven safe

**Why**: EVA checks the generated assertions, finding potential runtime errors.

### 3. **Code Safety Audit**
Understanding potential runtime errors:
- Identify all points where errors could occur
- Document safety assumptions
- Review error-prone code sections
- Plan testing strategies

**Why**: Makes all implicit safety requirements explicit.

### 4. **Legacy Code Analysis**
Analyzing existing code without annotations:
- Quick first-pass safety analysis
- No code modification required
- Identify dangerous operations
- Guide refactoring priorities

**Why**: Automatic process works on any C code.

### 5. **Teaching and Learning**
Educational purposes:
- Understanding C undefined behaviors
- Learning about runtime errors
- Seeing where checks are needed
- Training in formal methods

**Why**: Visualizes all the safety conditions programmers must ensure.

### 6. **Compliance Verification**
Meeting coding standards:
- MISRA C compliance checking
- DO-178C safety requirements
- ISO 26262 requirements
- General safety standards

**Why**: Explicitly shows what must be verified for safety compliance.

### 7. **Integration Testing Preparation**
Guiding test case generation:
- Identify boundary conditions
- Create test cases for edge cases
- Focus testing on dangerous operations
- Validate input ranges

**Why**: Shows exactly what conditions need testing.

### 8. **Multi-Analyzer Workflows**
As part of comprehensive analysis:
1. RTE generates annotations
2. EVA checks automatically provable ones
3. WP proves the remaining ones with specifications

**Why**: Efficient division of labor between analyzers.

## Running RTE

### Basic Usage

```bash
# Generate all runtime error annotations
frama-c -rte example.c
```

### With GUI

```bash
frama-c-gui -rte example.c
```

### Common Options

```bash
# Generate annotations and print annotated code
frama-c -rte -print example.c

# Generate only specific types of checks
frama-c -rte -rte-select mem example.c          # Memory access errors
frama-c -rte -rte-select div example.c          # Division by zero
frama-c -rte -rte-select signed-overflow example.c  # Signed integer overflow

# Generate for specific function
frama-c -rte -main my_function example.c

# Save annotated code to file
frama-c -rte -print -ocode annotated.c example.c

# Combine RTE with EVA
frama-c -rte -then -eva example.c

# Combine RTE with WP
frama-c -rte -then -wp example.c
```

## Types of Generated Annotations

### 1. Division by Zero

```c
int divide(int a, int b) {
    //@ assert rte: div_by_zero: b != 0;
    return a / b;
}
```

### 2. Array Bounds

```c
void access_array(int *arr, int i) {
    //@ assert rte: mem_access: \valid(arr + i);
    arr[i] = 0;
}
```

### 3. Integer Overflow

```c
int add(int a, int b) {
    //@ assert rte: signed_overflow: a + b <= INT_MAX;
    //@ assert rte: signed_underflow: a + b >= INT_MIN;
    return a + b;
}
```

### 4. Pointer Validity

```c
void deref(int *ptr) {
    //@ assert rte: mem_access: \valid(ptr);
    *ptr = 42;
}
```

### 5. Shift Operations

```c
int shift(int x, int n) {
    //@ assert rte: shift: 0 <= n < 32;
    return x << n;
}
```

## Typical Workflows

### Workflow 1: RTE + EVA

```bash
# Generate annotations and check with EVA
frama-c -rte -then -eva example.c
```

This workflow:
1. RTE generates runtime error assertions
2. EVA attempts to prove them automatically
3. Results show which operations are safe and which may fail

### Workflow 2: RTE + WP

```bash
# Generate annotations and prove with WP
frama-c -rte -then -wp example.c
```

This workflow:
1. RTE generates runtime error assertions
2. WP generates proof obligations
3. Theorem provers attempt to prove safety

### Workflow 3: RTE + EVA + WP

```bash
# Generate, check automatically, then prove remaining
frama-c -rte -then -eva -then -wp example.c
```

This workflow:
1. RTE generates annotations
2. EVA checks what it can automatically
3. WP proves remaining obligations

## Selective Annotation Generation

You can control which types of annotations RTE generates:

```bash
# Only memory access checks
-rte-select mem

# Only division by zero
-rte-select div

# Only signed overflow
-rte-select signed-overflow

# Only unsigned overflow
-rte-select unsigned-overflow

# Only shift operations
-rte-select shift

# Multiple types
-rte-select mem,div,signed-overflow
```

## Understanding RTE Output

After running RTE, the code is annotated with assertions like:

```c
/*@ assert rte: assertion_type: condition; */
```

Where:
- `rte`: Indicates it's an RTE-generated assertion
- `assertion_type`: The type of runtime error being checked
- `condition`: The logical condition that must hold

## Integration Best Practices

1. **Run RTE First**: Always generate annotations before analysis
2. **Review Generated Code**: Use `-print` to see what's generated
3. **Selective Generation**: Use `-rte-select` for focused analysis
4. **Combine with EVA**: Most effective when used together
5. **Add User Annotations**: Complement with your own specifications
6. **Save Annotated Code**: Use `-ocode` to preserve annotations

## Performance Tips

- RTE is generally fast and has minimal overhead
- For large codebases, use `-main` to focus on specific functions
- Use selective generation to reduce annotation volume
- Consider annotating incrementally by module

## Limitations

- **Context Insensitive**: Doesn't know if errors are actually possible
- **May Over-Annotate**: Generates checks for all potential errors
- **Requires Verification**: Annotations must still be checked
- **Platform Dependent**: Some checks depend on architecture (e.g., INT_MAX)

## Error Categories

### Memory Errors
- Null pointer dereference
- Invalid pointer access
- Array out-of-bounds
- Use after free

### Arithmetic Errors
- Division by zero
- Modulo by zero
- Signed integer overflow
- Unsigned integer overflow

### Shift Errors
- Shift by negative amount
- Shift by too large amount
- Shift of negative value (left shift)

### Downcast Errors
- Invalid pointer downcast
- Type punning errors

## Further Reading

- [RTE Plugin Documentation](https://frama-c.com/html/rte-manual/index.html)
- [C Undefined Behavior Guide](https://frama-c.com/html/undefined-behavior.html)
- [Combining Analyzers Tutorial](https://frama-c.com/html/tutorial-combining-analyzers.html)
