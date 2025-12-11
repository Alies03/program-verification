#include <stdint.h>
#include <assert.h>

// Original method
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

// Naive method
uint16_t karatsuba2(uint8_t x, uint8_t y){
	uint8_t x0 = x & 0x0F;
	uint8_t x1 = x >> 4;
	uint8_t y0 = y & 0x0F;
	uint8_t y1 = y >> 4;

	uint16_t z0 = (uint16_t)x0 * (uint16_t)y0;
	uint8_t z00 = z0 & 0x0F;
	uint8_t z01 = z0 >> 4;

	uint16_t sum_x = x0 + x1;
	uint16_t sum_y = y0 + y1;

	uint16_t z1 = (uint16_t)x0 * (uint16_t)y1 + 
	  (uint16_t)x1 * (uint16_t)y0 + z01;
    uint8_t z10 = z1 & 0x0F;
	uint8_t z11 = z1 >> 4;
	
	uint16_t z2 = (uint16_t)x1 * (uint16_t)y1 + z11;
      
	return (z2 << 8) | (z10 << 4) | z00;
}

// Optimized method
uint16_t karatsuba3(uint8_t x, uint8_t y){
	uint8_t x0 = x & 0x0F;
	uint8_t x1 = x >> 4;
	uint8_t y0 = y & 0x0F;
	uint8_t y1 = y >> 4;

	uint16_t z0 = (uint16_t)x0 * (uint16_t)y0;
	uint8_t z00 = z0 & 0x0F;
	uint8_t z01 = z0 >> 4;
	uint16_t z2 = (uint16_t)x1 * (uint16_t)y1;

	uint16_t sum_x = x0 + x1;
	uint16_t sum_y = y0 + y1;

	uint16_t z1 = (sum_x * sum_y) - z0 - z2 + z01;
	uint8_t z10 = z1 & 0x0F;
	uint8_t z11 = z1 >> 4;
	uint16_t z3 = z2+z11;

	return (z3 << 8) | (z10 << 4) | z00;
}

int main() {
    uint8_t x;
    uint8_t y;

    uint16_t result = karatsuba(x, y);
    uint16_t expected = x * y;
    assert(result == expected);

    return 0;
}
