int main()
{
	int sum = 0;
	int i = 0;
	int x = 1;

	while (i < 11) {
		sum = sum + i;
		i = i + 1;
		x = x * 2;
	}

	if (sum == 0) {
		sum = 10;
	} else {
		x = 30;
		if (i < 10) {
			x = x + i;
		} else {
			x = x + 2;
		}
		x = x + 40;
	}

	//assert(x != 0);
	int u;

	assert(u != 0);

	return 0;
}
