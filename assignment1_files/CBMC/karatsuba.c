#include <stdint.h>
#include <assert.h>

uint16_t karatsuba(uint8_t x, uint8_t y){
	uint8_t x0 = x & 0x0F;
	uint8_t x1 = x >> 4;
	uint8_t y0 = y & 0x0F;
	uint8_t y1 = y >> 4;

	uint16_t z0 = (uint16_t)x0 * (uint16_t)y0;
	uint16_t z2 = (uint16_t)x1 * (uint16_t)y1;

	uint16_t sum_x = x0 + x1;
	uint16_t sum_y = y0 + y1;

	uint16_t z1 = (sum_x * sum_y) - z0 - z2;

	return (z2 << 8) | (z1 << 4) | z0;
}