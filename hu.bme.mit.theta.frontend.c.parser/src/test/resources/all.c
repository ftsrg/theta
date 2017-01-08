#include <assert.h>

extern int nondet();

int main()
{
	int sum = 0, i = 0, x = 2;

	int y = nondet();

	long n = (long) sum;

	if (x == 0) {
		goto ERROR;
	} else {
		i = 3;
	}

	x = x + 1;

	if (i == 0) {
		goto ERROR;
	} else {
		goto out;
	}

/*
	if (i == 0) {
		goto ERROR;
	} else {
		goto out;
	} */

	/*
	 *
	switch (x) {
	case 1:
		sum = 1;
		break;
	case 2:
		sum = 2;
	case 3:
		i = 0;
		break;
	case 4:
	case 5:
		sum = 4;
		break;
	default:
		sum = 10;
	} */

	out: return 0;

	ERROR: assert(0);
	return 1;

}
