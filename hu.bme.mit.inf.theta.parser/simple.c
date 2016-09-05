int main()
{
	/*
	int x, y = 0, z = 0, b = 3;

	for (x = 0; x < 3; x += 1) {
		y = ++z;
		b = b + 1;
		if (b == 4) {
			continue;
		}
	}

	x++;

	assert(!(x < 0));
*/
	int sum = 0;
	int i = 1;
	while (i<11) {
		sum = sum + i;
		i = i + 1;
	}

	assert(i == 11);

	return 0;
}
