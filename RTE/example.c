/**
 * RTE (Runtime Error) Example
 * 
 * This example demonstrates various runtime errors that RTE can detect
 * by automatically generating ACSL assertions. RTE itself doesn't verify
 * the code but generates annotations that can be checked by EVA or WP.
 * 
 * To run RTE on this file:
 *   frama-c -rte example.c
 * 
 * To see the generated annotations:
 *   frama-c -rte -print example.c
 * 
 * To combine RTE with EVA:
 *   frama-c -rte -then -eva example.c
 * 
 * To combine RTE with WP:
 *   frama-c -rte -then -wp example.c
 */

#include <stdio.h>
#include <limits.h>

/**
 * Example 1: Division by zero
 * RTE will generate: assert rte: div_by_zero: divisor != 0;
 */
int divide(int dividend, int divisor) {
    // RTE generates assertion here to check divisor != 0
    return dividend / divisor;
}

/**
 * Example 2: Modulo by zero
 * RTE will generate: assert rte: mod_by_zero: divisor != 0;
 */
int modulo(int dividend, int divisor) {
    // RTE generates assertion here to check divisor != 0
    return dividend % divisor;
}

/**
 * Example 3: Array bounds checking
 * RTE will generate: assert rte: mem_access: \valid(array + index);
 */
int array_access(int* array, int index) {
    // RTE generates assertion to verify array[index] is valid
    return array[index];
}

/**
 * Example 4: Pointer dereference
 * RTE will generate: assert rte: mem_access: \valid(ptr);
 */
void pointer_deref(int* ptr) {
    // RTE generates assertion to check ptr is valid
    *ptr = 42;
}

/**
 * Example 5: Integer overflow (signed addition)
 * RTE will generate overflow checks for signed arithmetic
 */
int add_integers(int a, int b) {
    // RTE generates assertions for signed overflow/underflow
    return a + b;
}

/**
 * Example 6: Integer overflow (signed multiplication)
 * RTE will generate overflow checks
 */
int multiply_integers(int a, int b) {
    // RTE generates assertions for multiplication overflow
    return a * b;
}

/**
 * Example 7: Subtraction underflow
 * RTE checks for underflow in subtraction
 */
int subtract_integers(int a, int b) {
    // RTE generates assertions for signed underflow/overflow
    return a - b;
}

/**
 * Example 8: Left shift operations
 * RTE will verify shift amount is valid
 */
int left_shift(int value, int shift_amount) {
    // RTE generates assertions:
    // - shift_amount >= 0
    // - shift_amount < bit_width
    // - no overflow occurs
    return value << shift_amount;
}

/**
 * Example 9: Right shift operations
 * RTE will verify shift amount is valid
 */
int right_shift(int value, int shift_amount) {
    // RTE generates assertions for valid shift
    return value >> shift_amount;
}

/**
 * Example 10: Array with loop
 * RTE generates bounds checks for each array access
 */
void fill_array(int* array, int size, int value) {
    for (int i = 0; i < size; i++) {
        // RTE generates: assert rte: mem_access: \valid(array + i);
        array[i] = value;
    }
}

/**
 * Example 11: Pointer arithmetic
 * RTE checks validity of pointer arithmetic results
 */
int pointer_arithmetic(int* base, int offset) {
    // RTE generates assertions for valid pointer arithmetic
    int* ptr = base + offset;
    return *ptr;
}

/**
 * Example 12: Multi-dimensional array access
 * RTE checks all index operations
 */
int matrix_access(int matrix[][10], int row, int col) {
    // RTE generates bounds checks for row and col
    return matrix[row][col];
}

/**
 * Example 13: Structure field access through pointer
 * RTE checks pointer validity
 */
struct Point {
    int x;
    int y;
};

void set_point(struct Point* p, int x, int y) {
    // RTE generates: assert rte: mem_access: \valid(p);
    p->x = x;
    p->y = y;
}

/**
 * Example 14: Nested pointer dereference
 * RTE checks each level of indirection
 */
int nested_deref(int** ptr) {
    // RTE generates assertions for both levels
    return **ptr;
}

/**
 * Example 15: Complex expression with multiple operations
 * RTE generates checks for each operation
 */
int complex_expression(int a, int b, int c, int d) {
    // RTE generates checks for:
    // - multiplication overflow
    // - addition overflow
    // - division by zero
    // - final division by zero
    return (a * b + c) / d;
}

/**
 * Example 16: Array copy with pointer arithmetic
 * RTE checks all memory accesses
 */
void array_copy(int* dest, const int* src, int count) {
    for (int i = 0; i < count; i++) {
        // RTE generates validity checks for both pointers
        dest[i] = src[i];
    }
}

/**
 * Example 17: Conditional with potential division
 * RTE still generates checks even in conditionals
 */
int conditional_divide(int a, int b, int use_divide) {
    if (use_divide) {
        // RTE generates division by zero check
        return a / b;
    }
    return a;
}

/**
 * Example 18: String length with potential overflow
 * RTE checks array bounds and pointer arithmetic
 */
int string_length(const char* str) {
    int len = 0;
    // RTE generates checks for each array access
    while (str[len] != '\0') {
        len++;
    }
    return len;
}

/**
 * Example 19: Increment/Decrement operations
 * RTE checks for overflow in compound assignments
 */
void increment_operations(int* value) {
    // RTE generates overflow checks for each operation
    (*value)++;
    (*value)--;
    (*value) += 5;
    (*value) -= 3;
}

/**
 * Example 20: Switch statement with array access
 * RTE checks operations in each case
 */
int switch_array_access(int* array, int selector) {
    switch (selector) {
        case 0:
            return array[0];
        case 1:
            return array[1];
        case 2:
            return array[2];
        default:
            return array[selector];
    }
}

/**
 * Example 21: Function with multiple potential errors
 * Demonstrates how RTE catches various error types in one function
 */
int multiple_errors(int* array, int size, int index, int divisor) {
    // RTE generates:
    // 1. Array bounds check
    int value = array[index];
    
    // 2. Overflow check for multiplication
    int doubled = value * 2;
    
    // 3. Division by zero check
    int result = doubled / divisor;
    
    // 4. Another array access check
    array[index] = result;
    
    // 5. Overflow check for return addition
    return result + index;
}

/**
 * Example 22: Bitwise operations
 * RTE may generate checks for shift operations
 */
unsigned int bitwise_ops(unsigned int value, int shift) {
    // Shift operations are checked by RTE
    unsigned int shifted = value << shift;
    return shifted >> 1;
}

/**
 * Example 23: Ternary operator with division
 * RTE checks operations in both branches
 */
int ternary_divide(int a, int b, int c) {
    // RTE generates checks for both possible divisions
    return (a > 0) ? (b / a) : (c / a);
}

/**
 * Main function demonstrating RTE usage
 */
int main() {
    int array[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    int value = 100;
    int result;
    
    printf("=== RTE Example Program ===\n\n");
    
    // These operations will have RTE annotations generated
    printf("1. Division: ");
    result = divide(100, 5);
    printf("%d / %d = %d\n", 100, 5, result);
    
    printf("\n2. Array access: ");
    result = array_access(array, 5);
    printf("array[5] = %d\n", result);
    
    printf("\n3. Pointer operations: ");
    pointer_deref(&value);
    printf("value = %d\n", value);
    
    printf("\n4. Integer arithmetic: ");
    result = add_integers(10, 20);
    printf("10 + 20 = %d\n", result);
    
    printf("\n5. Array filling: ");
    fill_array(array, 10, 42);
    printf("Array filled with 42\n");
    
    printf("\n6. Complex expression: ");
    result = complex_expression(2, 3, 4, 5);
    printf("(2 * 3 + 4) / 5 = %d\n", result);
    
    printf("\n=== RTE Analysis Complete ===\n");
    printf("\nTo see RTE annotations:\n");
    printf("  frama-c -rte -print example.c\n\n");
    printf("To verify with EVA:\n");
    printf("  frama-c -rte -then -eva example.c\n\n");
    printf("To prove with WP:\n");
    printf("  frama-c -rte -then -wp example.c\n");
    
    return 0;
}

/**
 * RTE Analysis Workflow:
 * 
 * Step 1: Generate annotations
 *   frama-c -rte example.c
 * 
 * Step 2: View annotated code
 *   frama-c -rte -print example.c
 * 
 * Step 3: Save annotated code
 *   frama-c -rte -print -ocode annotated.c example.c
 * 
 * Step 4: Verify with EVA
 *   frama-c -rte -then -eva example.c
 * 
 * Step 5: Prove with WP
 *   frama-c -rte -then -wp example.c
 * 
 * Selective annotation generation:
 *   frama-c -rte -rte-select mem example.c          # Only memory errors
 *   frama-c -rte -rte-select div example.c          # Only division errors
 *   frama-c -rte -rte-select signed-overflow example.c  # Only overflows
 */
