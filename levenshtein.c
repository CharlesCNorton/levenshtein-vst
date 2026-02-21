#include <stddef.h>
#include <stdlib.h>

/* Levenshtein distance (Wagner-Fischer algorithm).
   Based on https://github.com/wooorm/levenshtein.c (MIT license).
   Simplified for VST verification: removed pointer-equality shortcut,
   replaced SIZE_MAX trick with straightforward loop. */

size_t
levenshtein_n(const char *a, const size_t length,
              const char *b, const size_t bLength) {
  size_t *cache;
  size_t index;
  size_t bIndex;
  size_t distance;
  size_t bDistance;
  size_t result;
  char code;

  /* Initialize once so VST can track _result before the outer loop. */
  result = 0;

  if (length == 0) {
    return bLength;
  }

  if (bLength == 0) {
    return length;
  }

  cache = (size_t *)calloc(length, sizeof(size_t));

  /* Initialize the vector: cache[i] = i + 1. */
  index = 0;
  while (index < length) {
    cache[index] = index + 1;
    index++;
  }

  /* Main DP loop. */
  bIndex = 0;
  while (bIndex < bLength) {
    code = b[bIndex];
    result = bIndex;
    distance = bIndex;
    bIndex++;

    index = 0;
    while (index < length) {
      if (code == a[index]) {
        bDistance = distance;
      } else {
        bDistance = distance + 1;
      }
      distance = cache[index];

      if (distance > result) {
        if (bDistance > result) {
          result = result + 1;
        } else {
          result = bDistance;
        }
      } else {
        if (bDistance > distance) {
          result = distance + 1;
        } else {
          result = bDistance;
        }
      }
      cache[index] = result;

      index++;
    }
  }

  free(cache);

  return result;
}
