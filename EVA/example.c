/**
 * EVA (Evolved Value Analysis) Example
 * 
 * This example demonstrates various scenarios that EVA can analyze:
 * 1. Buffer overflow detection
 * 2. Division by zero detection
 * 3. Uninitialized variable usage
 * 4. Array bounds checking
 * 5. Pointer validity checking
 * 
 * To run EVA on this file:
 *   frama-c -eva example.c
 * 
 * To run with GUI:
 *   frama-c-gui -eva example.c
 */

#include <stdio.h>
#include <string.h>
#include <limits.h>

/**
 * Example 1: Buffer overflow detection
 * EVA will detect potential array out-of-bounds access
 */
void buffer_example(int index) {
    int buffer[10];
    int i;
    
    // Initialize buffer
    for (i = 0; i < 10; i++) {
        buffer[i] = i * 2;
    }
    
    // Safe access - EVA will verify this is OK
    if (index >= 0 && index < 10) {
        printf("Safe access: buffer[%d] = %d\n", index, buffer[index]);
    }
    
    // Potentially unsafe - EVA will raise an alarm if index can be out of bounds
    // Uncomment to see EVA detect the issue:
    // printf("Unsafe: buffer[%d] = %d\n", index, buffer[index]);
}

/**
 * Example 2: Division by zero detection
 * EVA will analyze if divisor can be zero
 */
int safe_divide(int numerator, int denominator) {
    // EVA will check if denominator can be zero
    if (denominator != 0) {
        return numerator / denominator;
    }
    return 0;
}

int unsafe_divide(int numerator, int denominator) {
    // EVA will raise an alarm here if denominator might be zero
    return numerator / denominator;
}

/**
 * Example 3: Pointer validity checking
 * EVA tracks pointer values and checks for null dereferences
 */
void pointer_example(int* ptr) {
    // Safe: check before dereference
    if (ptr != NULL) {
        *ptr = 42;
        printf("Set value to: %d\n", *ptr);
    }
    
    // Unsafe: direct dereference - EVA will warn if ptr can be NULL
    // Uncomment to see the alarm:
    // *ptr = 100;
}

/**
 * Example 4: Array bounds with loop
 * EVA analyzes loop behavior and array accesses
 */
void loop_array_example() {
    int data[20];
    int i;
    
    // Safe loop - bounds are clear
    for (i = 0; i < 20; i++) {
        data[i] = i * i;
    }
    
    // Print some values
    for (i = 0; i < 5; i++) {
        printf("data[%d] = %d\n", i, data[i]);
    }
}

/**
 * Example 5: String operations with potential buffer overflow
 * EVA can detect unsafe string manipulations
 */
void string_example(const char* input) {
    char buffer[16];
    
    // Safe: using strncpy with proper bounds
    if (input != NULL) {
        strncpy(buffer, input, sizeof(buffer) - 1);
        buffer[sizeof(buffer) - 1] = '\0';
        printf("Copied string: %s\n", buffer);
    }
    
    // Unsafe strcpy would be detected by EVA
    // Uncomment to see the alarm:
    // strcpy(buffer, input);  // Buffer overflow if input is too long!
}

/**
 * Example 6: Complex pointer arithmetic
 * EVA tracks pointer values through arithmetic operations
 */
void pointer_arithmetic_example() {
    int array[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    int* ptr = array;
    int* end = array + 10;
    
    // Safe: pointer stays within bounds
    while (ptr < end) {
        printf("%d ", *ptr);
        ptr++;
    }
    printf("\n");
}

/**
 * Example 7: Integer overflow detection
 * EVA can detect potential integer overflows
 */
int add_with_check(int a, int b) {
    // Check for overflow before addition
    if (a > 0 && b > 0 && a > (INT_MAX - b)) {
        return INT_MAX;  // Overflow would occur
    }
    if (a < 0 && b < 0 && a < (INT_MIN - b)) {
        return INT_MIN;  // Underflow would occur
    }
    return a + b;
}

/**
 * Example 8: Uninitialized variable detection
 * EVA tracks variable initialization
 */
void initialization_example() {
    int initialized = 10;
    int uninitialized;
    
    // Safe: using initialized variable
    printf("Initialized: %d\n", initialized);
    
    // Unsafe: using uninitialized variable
    // Uncomment to see EVA detect this:
    // printf("Uninitialized: %d\n", uninitialized);
    
    // After initialization, it's safe
    uninitialized = 20;
    printf("Now initialized: %d\n", uninitialized);
}

/**
 * Example 9: Function with preconditions
 * Using ACSL annotations to specify input constraints
 */
/*@
  requires 0 <= x <= 100;
  requires 0 <= y <= 100;
  ensures \result >= 0;
  ensures \result <= 200;
*/
int bounded_add(int x, int y) {
    return x + y;
}

/**
 * Example 10: Array search with bounds checking
 */
/*@
  requires \valid(arr + (0..size-1));
  requires size > 0;
  assigns \nothing;
*/
int find_value(int* arr, int size, int value) {
    int i;
    for (i = 0; i < size; i++) {
        if (arr[i] == value) {
            return i;
        }
    }
    return -1;  // Not found
}

/**
 * Main function demonstrating EVA analysis
 */
int main() {
    int test_array[5] = {10, 20, 30, 40, 50};
    int result;
    
    printf("=== EVA Example Program ===\n\n");
    
    // Test buffer example
    printf("1. Buffer example:\n");
    buffer_example(5);  // Safe index
    
    // Test division
    printf("\n2. Division example:\n");
    result = safe_divide(100, 5);
    printf("100 / 5 = %d\n", result);
    
    // Test pointer example
    printf("\n3. Pointer example:\n");
    int value = 0;
    pointer_example(&value);
    
    // Test loop array
    printf("\n4. Loop array example:\n");
    loop_array_example();
    
    // Test string operations
    printf("\n5. String example:\n");
    string_example("Hello, EVA!");
    
    // Test pointer arithmetic
    printf("\n6. Pointer arithmetic:\n");
    pointer_arithmetic_example();
    
    // Test bounded addition
    printf("\n7. Bounded addition:\n");
    result = bounded_add(50, 75);
    printf("50 + 75 = %d\n", result);
    
    // Test array search
    printf("\n8. Array search:\n");
    result = find_value(test_array, 5, 30);
    printf("Found 30 at index: %d\n", result);
    
    // Test initialization
    printf("\n9. Initialization example:\n");
    initialization_example();
    
    printf("\n=== EVA Analysis Complete ===\n");
    printf("Run: frama-c -eva example.c\n");
    printf("Or with GUI: frama-c-gui -eva example.c\n");
    
    return 0;
}
