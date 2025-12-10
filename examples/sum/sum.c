#include <stddef.h>

int sum(int *arr, size_t n) {
  int total = 0;
  for (size_t i = 0; i < n; i++) {
    total += arr[i];
  }
  return total;
}
