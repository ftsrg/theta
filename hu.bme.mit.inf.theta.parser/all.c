#include <assert.h>

extern int nondet();

int main()
{
	int sum = 0, i = 0, x = 2;

	int y = nondet();

	if (x == 0)
		goto err;


	out:
		return 0;
	err:
		return 0;

/*
	if (x == 0) {
		i = 1;
	} else {
		i = 3;
	}

	if (i == 0) {
		sum = 1;
	} else {
		sum = 3;
	}

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
	}

	assert(i != 0);
	assert(sum != 0);

	return 0;*/
}
