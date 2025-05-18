#include <stdint.h>

//@ requires true;
//@ ensures true;
int32_t add(int32_t a, int32_t b) {
    return a + b;
}