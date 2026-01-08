/**
 * WP (Weakest Precondition) Example
 * 
 * This example demonstrates formal verification using ACSL annotations
 * and the WP plugin for deductive verification.
 * 
 * To run WP on this file:
 *   frama-c -wp example.c
 * 
 * To run with GUI:
 *   frama-c-gui -wp example.c
 * 
 * To use specific prover:
 *   frama-c -wp -wp-prover alt-ergo,z3 example.c
 */

#include <stddef.h>
#include <limits.h>

/**
 * Example 1: Simple function with precondition and postcondition
 * This proves the function always returns non-negative result
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
 * Example 2: Maximum of two integers
 * Proves the result is greater than or equal to both inputs
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
 * Example 3: Absolute value
 * Proves the result is always non-negative
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
 * Example 4: Array initialization
 * Proves all elements are set to the given value
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
 * Example 5: Array sum
 * Computes the sum of array elements
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
 * Example 6: Linear search
 * Proves that if result is non-negative, the value is found at that index
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

/**
 * Example 7: Safe division
 * Proves no division by zero occurs
 */
/*@
  requires divisor != 0;
  ensures divisor * \result == dividend || divisor * \result == dividend - (dividend % divisor);
  assigns \nothing;
*/
int safe_divide(int dividend, int divisor) {
    return dividend / divisor;
}

/**
 * Example 8: Bounded increment
 * Proves no integer overflow
 */
/*@
  requires x < INT_MAX;
  ensures \result == x + 1;
  ensures \result > x;
  assigns \nothing;
*/
int increment(int x) {
    return x + 1;
}

/**
 * Example 9: Swap two integers
 * Proves values are exchanged correctly
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

/**
 * Example 10: Array copy
 * Proves all elements are copied correctly
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
 * Example 11: Factorial (iterative)
 * Proves basic properties of factorial computation
 */
/*@
  requires n >= 0;
  requires n <= 12;  // Prevent overflow for typical int size
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
 * Example 12: Count occurrences
 * Counts how many times a value appears in an array
 */
/*@
  requires \valid_read(arr + (0..size-1));
  requires size >= 0;
  ensures \result >= 0;
  ensures \result <= size;
  assigns \nothing;
*/
int count_occurrences(const int* arr, int size, int value) {
    int count = 0;
    
    /*@
      loop invariant 0 <= i <= size;
      loop invariant 0 <= count <= i;
      loop assigns i, count;
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        if (arr[i] == value) {
            count++;
        }
    }
    
    return count;
}

/**
 * Example 13: Check if array is sorted
 * Verifies the function correctly determines if array is sorted
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
 * Example 14: Minimum value in array
 * Proves the result is indeed the minimum
 */
/*@
  requires \valid_read(arr + (0..size-1));
  requires size > 0;
  ensures \forall integer i; 0 <= i < size ==> \result <= arr[i];
  ensures \exists integer i; 0 <= i < size && \result == arr[i];
  assigns \nothing;
*/
int array_min(const int* arr, int size) {
    int min = arr[0];
    
    /*@
      loop invariant 1 <= i <= size;
      loop invariant \forall integer k; 0 <= k < i ==> min <= arr[k];
      loop invariant \exists integer k; 0 <= k < i && min == arr[k];
      loop assigns i, min;
      loop variant size - i;
    */
    for (int i = 1; i < size; i++) {
        if (arr[i] < min) {
            min = arr[i];
        }
    }
    
    return min;
}

/**
 * Example 15: In-place array reversal
 * Proves the array is reversed correctly
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
      loop invariant \forall integer i; 0 <= i < left ==> 
        arr[i] == \old(arr[size - 1 - i]);
      loop invariant \forall integer i; right < i < size ==> 
        arr[i] == \old(arr[size - 1 - i]);
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
 * Main function for testing
 * Note: WP focuses on proving properties, not executing code
 */
int main() {
    // These calls demonstrate the verified functions
    // WP proves properties statically, without execution
    
    int result;
    int array[5] = {1, 2, 3, 4, 5};
    
    result = add_positive(10, 20);
    result = max(5, 10);
    result = absolute(-15);
    
    array_init(array, 5, 0);
    result = array_sum(array, 5);
    result = linear_search(array, 5, 0);
    
    result = factorial(5);
    result = is_sorted(array, 5);
    
    return 0;
}

/**
 * Running WP on this file:
 * 
 * Basic verification:
 *   frama-c -wp example.c
 * 
 * With specific provers:
 *   frama-c -wp -wp-prover alt-ergo,z3 example.c
 * 
 * With increased timeout:
 *   frama-c -wp -wp-timeout 30 example.c
 * 
 * With GUI for interactive analysis:
 *   frama-c-gui -wp example.c
 * 
 * Focus on specific function:
 *   frama-c -wp -wp-fct array_reverse example.c
 * 
 * Generate detailed report:
 *   frama-c -wp -wp-report example.c
 */
