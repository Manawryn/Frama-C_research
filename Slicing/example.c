/**
 * Slicing Example
 * 
 * This example demonstrates program slicing with various scenarios.
 * Slicing extracts only the code that affects specific program points.
 * 
 * To run slicing on this file (slice on main's return value):
 *   frama-c -slice-return main example.c
 * 
 * To export the sliced code:
 *   frama-c -slice-return main -then-on 'Slicing export' -print example.c
 * 
 * To save sliced code to a file:
 *   frama-c -slice-return main -then-on 'Slicing export' -print -ocode sliced.c example.c
 * 
 * To use GUI:
 *   frama-c-gui -slice-return main example.c
 */

#include <stdio.h>

/**
 * Global variables for demonstration
 */
int global_counter = 0;
int global_unused = 0;

/**
 * Example 1: Simple computation with relevant and irrelevant code
 * When slicing on return value, unrelated code is removed
 */
int simple_function(int x) {
    int relevant = x * 2;           // Affects return value
    int irrelevant = 100;           // Doesn't affect return value
    
    global_unused = irrelevant;     // Not in slice
    
    return relevant;                // Slicing criterion
}

/**
 * Example 2: Conditional with both branches relevant
 * Slicing keeps the condition and both branches
 */
int conditional_function(int x) {
    int result;
    
    if (x > 0) {
        result = x * 2;
    } else {
        result = x * 3;
    }
    
    return result;
}

/**
 * Example 3: Mix of relevant and irrelevant statements
 * Only statements affecting the return are kept
 */
int mixed_function(int a, int b, int c) {
    int x = a + b;          // Relevant: affects result
    int y = c * 2;          // Irrelevant: not used
    int z = x * 2;          // Relevant: affects result
    
    printf("Debug: %d\n", y);  // Irrelevant
    
    return z;
}

/**
 * Example 4: Loop with counter
 * Slicing keeps loop structure and relevant operations
 */
int sum_array(int* array, int size) {
    int sum = 0;            // Relevant
    int count = 0;          // May be irrelevant if not used
    
    for (int i = 0; i < size; i++) {
        sum += array[i];    // Relevant
        count++;            // Irrelevant for sum
    }
    
    // If we slice on sum, count operations are removed
    return sum;
}

/**
 * Example 5: Function calls
 * Slicing includes called functions if they affect result
 */
int helper_relevant(int x) {
    return x * 2;
}

int helper_irrelevant(int x) {
    return x + 100;
}

int function_with_calls(int x) {
    int a = helper_relevant(x);     // Relevant
    int b = helper_irrelevant(x);   // Irrelevant
    
    return a;  // Only uses 'a', so helper_irrelevant is removed
}

/**
 * Example 6: Pointer operations
 * Slicing tracks data flow through pointers
 */
void modify_pointer(int* ptr, int value) {
    *ptr = value * 2;
}

int pointer_function(int x) {
    int result = 0;
    int dummy = 0;
    
    modify_pointer(&result, x);     // Relevant
    modify_pointer(&dummy, x);      // Irrelevant
    
    return result;
}

/**
 * Example 7: Multiple outputs
 * Demonstrates slicing on different criteria
 */
void compute_both(int input, int* output1, int* output2) {
    // Code for output1
    *output1 = input * 2;
    
    // Code for output2
    *output2 = input * 3;
}

/**
 * Example 8: Control dependency
 * Conditions that control execution are kept
 */
int control_dependency_example(int x) {
    int result = 0;
    
    // This condition controls whether result is modified
    if (x > 10) {
        result = x * 2;
    }
    // Condition is kept because it affects whether assignment happens
    
    return result;
}

/**
 * Example 9: Data dependency chain
 * Shows transitive dependencies
 */
int dependency_chain(int a) {
    int b = a + 1;      // b depends on a
    int c = b * 2;      // c depends on b
    int d = c + 3;      // d depends on c
    int e = a - 1;      // e depends on a but not used
    
    return d;           // All of a->b->c->d chain is relevant
}

/**
 * Example 10: Array processing with slice pragma
 */
int array_processing(int* data, int size) {
    int sum = 0;
    int product = 1;
    int max = data[0];
    
    for (int i = 0; i < size; i++) {
        sum += data[i];
        product *= data[i];
        
        if (data[i] > max) {
            max = data[i];
        }
    }
    
    // Slicing pragma to slice on specific variable
    //@ slice pragma expr sum;
    
    // When slicing on 'sum', only sum-related code is kept
    return sum;
}

/**
 * Example 11: Nested function calls
 * Shows inter-procedural slicing
 */
int level3(int x) {
    return x + 1;
}

int level2(int x) {
    int temp = level3(x);
    return temp * 2;
}

int level1(int x) {
    int result = level2(x);
    return result + 3;
}

/**
 * Example 12: Multiple return paths
 * All paths affecting return value are kept
 */
int multiple_returns(int x) {
    int a = x * 2;
    int b = x + 10;
    
    if (x < 0) {
        return a;       // Path 1
    }
    
    if (x > 100) {
        return b;       // Path 2
    }
    
    return a + b;       // Path 3
}

/**
 * Example 13: Dead code that will be eliminated
 */
int dead_code_example(int x) {
    int result = x * 2;
    
    // This code never affects result
    int dead = 999;
    dead = dead + 1;
    dead = dead * 2;
    
    return result;
}

/**
 * Example 14: Global variable usage
 * Tracks global variable dependencies
 */
int use_global(int x) {
    global_counter += x;    // Modifies global
    
    return global_counter;  // Uses global
}

/**
 * Example 15: Switch statement
 * Relevant cases are kept
 */
int switch_example(int selector, int value) {
    int result;
    
    switch (selector) {
        case 1:
            result = value * 2;
            break;
        case 2:
            result = value * 3;
            break;
        case 3:
            result = value * 4;
            break;
        default:
            result = value;
    }
    
    return result;
}

/**
 * Example 16: Slice on function calls
 * Demonstrates -slice-calls option
 */
void important_operation(int x) {
    printf("Important: %d\n", x);
}

void example_with_important_call(int a, int b) {
    int x = a + b;
    important_operation(x);
    
    int y = a - b;  // If slicing on important_operation call, y is irrelevant
}

/**
 * Example 17: Complex control flow
 */
int complex_control(int x, int y) {
    int result = 0;
    
    for (int i = 0; i < x; i++) {
        if (i % 2 == 0) {
            result += y;
        } else {
            result += y * 2;
        }
    }
    
    return result;
}

/**
 * Example 18: Struct operations
 */
struct Data {
    int value1;
    int value2;
    int value3;
};

int use_struct(struct Data* d) {
    // Slicing will determine which fields are relevant
    d->value1 = 10;
    d->value2 = 20;
    d->value3 = 30;
    
    return d->value1 + d->value2;  // value3 operations might be sliced out
}

/**
 * Example 19: Recursive function
 * Slicing handles recursion
 */
int recursive_sum(int n) {
    if (n <= 0) {
        return 0;
    }
    return n + recursive_sum(n - 1);
}

/**
 * Main function for demonstration
 */
int main() {
    int array[5] = {1, 2, 3, 4, 5};
    int result;
    
    printf("=== Slicing Example Program ===\n\n");
    
    // Various function calls
    result = simple_function(10);
    printf("Simple: %d\n", result);
    
    result = conditional_function(5);
    printf("Conditional: %d\n", result);
    
    result = mixed_function(1, 2, 3);
    printf("Mixed: %d\n", result);
    
    result = sum_array(array, 5);
    printf("Sum: %d\n", result);
    
    result = function_with_calls(7);
    printf("With calls: %d\n", result);
    
    result = dependency_chain(5);
    printf("Chain: %d\n", result);
    
    result = level1(10);
    printf("Nested: %d\n", result);
    
    // The final result affects main's return value
    // When slicing on main's return, all code affecting 'result' is kept
    return result;
}

/**
 * Slicing Commands:
 * 
 * Basic slicing on main's return:
 *   frama-c -slice-return main example.c
 * 
 * Slice on specific function:
 *   frama-c -slice-return sum_array example.c
 * 
 * Slice on function calls:
 *   frama-c -slice-calls important_operation example.c
 * 
 * Print sliced code:
 *   frama-c -slice-return main -then-on 'Slicing export' -print example.c
 * 
 * Export to file:
 *   frama-c -slice-return main -then-on 'Slicing export' -print -ocode sliced.c example.c
 * 
 * With GUI:
 *   frama-c-gui -slice-return main example.c
 * 
 * Slice on pragma:
 *   frama-c -slice-pragma sum example.c
 * 
 * Multiple criteria:
 *   frama-c -slice-return main -slice-return helper_relevant example.c
 * 
 * Combine with EVA:
 *   frama-c -slice-return main -then-on 'Slicing export' -eva example.c
 * 
 * Verbose output:
 *   frama-c -slice-return main -slice-verbose 2 example.c
 */
