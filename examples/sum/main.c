#include <stddef.h>
#include <stdio.h>
#include "sum.h"

static int read_ints(FILE *f, int *arr, size_t n) {
  for (size_t i = 0; i < n; i++) {
    if (fscanf(f, "%d", &arr[i]) != 1) {
      return -1;
    }
  }
  return 0;
}

int main() {
  int arr[5];
  if (read_ints(stdin, arr, 5) != 0) {
    return 1;
  }
  int res = sum(arr, 5);
  printf("Sum: %d\n", res);
}
