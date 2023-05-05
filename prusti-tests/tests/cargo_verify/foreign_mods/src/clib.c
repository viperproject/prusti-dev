#include <stdint.h>

int32_t max(int32_t a, int32_t b) {
	return a > b ? a : b;
}

void unannotated(void) {
}

int32_t abs(int32_t a) {
	return a >= 0 ? a : -a;
}
