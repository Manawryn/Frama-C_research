/**
 * WP (Weakest Precondition) Example
 * * This file contains a progressive series of examples for Frama-C WP.
 * It ranges from simple arithmetic to array manipulation and loops.
 * * HOW TO RUN:
 * 1. Basic check:
 * frama-c -wp example.c
 * * 2. With specific provers (if installed):
 * frama-c -wp -wp-prover alt-ergo,z3 example.c
 * * 3. Inspect the goals in the GUI:
 * frama-c-gui -wp example.c
 */

#include <stddef.h>
#include <limits.h>

/* =========================================================================
 * PART 1: Basic Arithmetic & Contracts
 * ========================================================================= */

/**
 * Example 1: Simple function with precondition and postcondition.
 * Proves the function always returns a non-negative result matching the sum.
 */
/*@
  requires x >= 0;
  requires y >= 0;
  ensures \result >= 0;
  ensures \result == x + y;
  assigns \nothing;
*/
int add_positive(int x, int y) {
    return x + y;
}

/**
 * Example 2: Maximum of two integers.
 * Proves post-conditions using conditional paths.
 */
/*@
  ensures \result >= a && \result >= b;
  ensures \result == a || \result == b;
  assigns \nothing;
*/
int max(int a, int b) {
    if (a > b)
        return a;
    else
        return b;
}

/**
 * Example 3: Absolute value.
 * Uses implication (==>) in post-conditions.
 */
/*@
  ensures \result >= 0;
  ensures (x >= 0 ==> \result == x);
  ensures (x < 0 ==> \result == -x);
  assigns \nothing;
*/
int absolute(int x) {
    if (x < 0)
        return -x;
    return x;
}

/**
 * Example 4: Safe division.
 * Proves absence of runtime errors (division by zero).
 */
/*@
  requires divisor != 0;
  ensures divisor * \result == dividend || divisor * \result == dividend - (dividend % divisor);
  assigns \nothing;
*/
int safe_divide(int dividend, int divisor) {
    return dividend / divisor;
}

/* =========================================================================
 * PART 2: Pointers & Swapping
 * ========================================================================= */

/**
 * Example 5: Swap two integers.
 * Demonstrates \old, \separated, and pointer validity.
 */
/*@
  requires \valid(a) && \valid(b);
  requires \separated(a, b);
  ensures *a == \old(*b);
  ensures *b == \old(*a);
  assigns *a, *b;
*/
void swap(int* a, int* b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}

/* =========================================================================
 * PART 3: Arrays & Loops (Basic)
 * ========================================================================= */

/**
 * Example 6: Array initialization.
 * Demonstrates loop invariants and quantifiers (\forall).
 */
/*@
  requires \valid(arr + (0..size-1));
  requires size >= 0;
  ensures \forall integer i; 0 <= i < size ==> arr[i] == value;
  assigns arr[0..size-1];
*/
void array_init(int* arr, int size, int value) {
    /*@
      loop invariant 0 <= i <= size;
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] == value;
      loop assigns i, arr[0..size-1];
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        arr[i] = value;
    }
}

/**
 * Example 7: Array sum.
 * Demonstrates accumulating values in a loop.
 */
/*@
  requires \valid_read(arr + (0..size-1));
  requires size >= 0;
  assigns \nothing;
*/
int array_sum(const int* arr, int size) {
    int sum = 0;
    
    /*@
      loop invariant 0 <= i <= size;
      loop assigns i, sum;
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        sum += arr[i];
    }
    
    return sum;
}

/**
 * Example 8: Linear search.
 * Proves search correctness (found vs not found).
 */
/*@
  requires \valid_read(arr + (0..size-1));
  requires size >= 0;
  ensures \result >= 0 ==> 0 <= \result < size && arr[\result] == value;
  ensures \result == -1 ==> \forall integer i; 0 <= i < size ==> arr[i] != value;
  assigns \nothing;
*/
int linear_search(const int* arr, int size, int value) {
    /*@
      loop invariant 0 <= i <= size;
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] != value;
      loop assigns i;
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        if (arr[i] == value) {
            return i;
        }
    }
    return -1;
}

/* =========================================================================
 * PART 4: Advanced Properties & Logic
 * ========================================================================= */

/**
 * Example 9: Check if array is sorted.
 * Uses nested quantification logic implicitly.
 */
/*@
  requires \valid_read(arr + (0..size-1));
  requires size >= 0;
  ensures \result == 0 || \result == 1;
  ensures \result == 1 ==> 
    \forall integer i, j; 0 <= i < j < size ==> arr[i] <= arr[j];
  assigns \nothing;
*/
int is_sorted(const int* arr, int size) {
    if (size <= 1) {
        return 1;
    }
    
    /*@
      loop invariant 1 <= i <= size;
      loop assigns i;
      loop variant size - i;
    */
    for (int i = 1; i < size; i++) {
        if (arr[i] < arr[i-1]) {
            return 0;
        }
    }
    
    return 1;
}

/**
 * Example 10: Array copy.
 * Uses \old inside ensures, but correctly avoids it in loop.
 */
/*@
  requires \valid(dest + (0..size-1));
  requires \valid_read(src + (0..size-1));
  requires \separated(dest + (0..size-1), src + (0..size-1));
  requires size >= 0;
  ensures \forall integer i; 0 <= i < size ==> dest[i] == \old(src[i]);
  assigns dest[0..size-1];
*/
void array_copy(int* dest, const int* src, int size) {
    /*@
      loop invariant 0 <= i <= size;
      loop invariant \forall integer k; 0 <= k < i ==> dest[k] == src[k];
      loop assigns i, dest[0..size-1];
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        dest[i] = src[i];
    }
}

/**
 * Example 11: In-place array reversal (CORRECTED).
 * Uses \at(..., Pre) inside loop invariants to refer to initial state.
 */
/*@
  requires \valid(arr + (0..size-1));
  requires size >= 0;
  ensures \forall integer i; 0 <= i < size ==> 
    arr[i] == \old(arr[size - 1 - i]);
  assigns arr[0..size-1];
*/
void array_reverse(int* arr, int size) {
    int left = 0;
    int right = size - 1;
    
    /*@
      loop invariant 0 <= left <= size;
      loop invariant -1 <= right < size;
      loop invariant left + right == size - 1;
      
      // CORRECTED: Used \at(..., Pre) instead of \old(...)
      loop invariant \forall integer i; 0 <= i < left ==> 
        arr[i] == \at(arr[size - 1 - i], Pre);
        
      // CORRECTED: Used \at(..., Pre) instead of \old(...)
      loop invariant \forall integer i; right < i < size ==> 
        arr[i] == \at(arr[size - 1 - i], Pre);
        
      loop assigns left, right, arr[0..size-1];
      loop variant right - left;
    */
    while (left < right) {
        int temp = arr[left];
        arr[left] = arr[right];
        arr[right] = temp;
        left++;
        right--;
    }
}

/**
 * Example 12: Factorial (iterative).
 * Includes bounds check to prevent integer overflow.
 */
/*@
  requires n >= 0;
  requires n <= 12;  // Prevent overflow for 32-bit int
  ensures \result >= 1;
  assigns \nothing;
*/
int factorial(int n) {
    int result = 1;
    
    /*@
      loop invariant 0 <= i <= n + 1;
      loop invariant result >= 1;
      loop assigns i, result;
      loop variant n + 1 - i;
    */
    for (int i = 1; i <= n; i++) {
        result *= i;
    }
    
    return result;
}

/**
 * Main function.
 * WP ignores the main function body unless specified, but checks calls.
 */
int main() {
    int result;
    int array[5] = {1, 2, 3, 4, 5};
    int dest[5];
    
    result = add_positive(10, 20);
    result = max(5, 10);
    result = absolute(-15);
    
    array_init(array, 5, 0);
    result = array_sum(array, 5);
    result = linear_search(array, 5, 0);
    
    swap(&array[0], &array[1]);
    array_copy(dest, array, 5);
    array_reverse(array, 5);
    
    result = factorial(5);
    result = is_sorted(array, 5);
    
    return 0;
}