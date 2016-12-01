int main() {
	int i, x, j = 3, u = 4, z, y;

	i = 3;
	x = 4;

	int sum = 0;

	if (x == 3) {
		u = 3;
		if (u == 3) {
			goto LAB0;
		}
		x = 4;
		z = 2;
	}

	while (i < 10) {
		sum = sum + i;
		i = i + 1;
	}

	LAB0: if (j == 5) {
		x = x + 1;
	}

	u = 6;


	return 0;
}
