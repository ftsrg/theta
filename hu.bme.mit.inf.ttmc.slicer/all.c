int main()
{
	int sum = 0;
	int i = 1;

	if (sum == 3) {
		sum = 0;
		if (sum == 0) {
			sum = 4;
		}
	} else {
		i = 1;
	}

	if (sum == 4) {
		while (i < 3) {
			sum = sum * 2;
		}
		sum = 0;
	}

	while (i < 11) {
		sum = sum + 1;
		i = i + 1;
	}

	return 0;
}
