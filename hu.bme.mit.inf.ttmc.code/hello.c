
int main(void) {
	int i, x, j = 3, u = 4, z, y;

	i = 3;

	if (i > 0) {
		i = 4;
	}

	i = (x, ++y, u++);

	x = y = z = u;

	if (x == 3) {
		int u = 3;
		u = u + 1;
	}

	while (u < 6) {
		u++;
		++u;
		z = u++ + j++;
		while (z < 8) {
			if (z == 3) {
				break;
			} else {
				continue;
			}
		}
		if (u == 3) {
			continue;
		}
		u = u + 1;
		if (u >= 5) {
			u = u - 2;
			break;
		}
	}

	for (int j = 0; j < 10; j++) {
		i++;
		if (j > 3)
			break;
	}

	switch(x) {
	case 1:
		x = 1;
		break;
	case 2:
	case 3:
		x = 3;
		break;
	case 4:
		x = 4;
	case 5:
		x = 5;
		break;
	case 6:
		x = 6;
	default:
		x = 7;
		break;
	}

	return 0;
}
