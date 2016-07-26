package hu.bme.mit.inf.ttmc.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Lt;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.add;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.asString;
import static java.lang.Math.max;
import static java.lang.Math.min;

import java.util.function.IntBinaryOperator;

import hu.bme.mit.inf.ttmc.common.matrix.IntMatrix;

final class SimpleDBM {

	private final int nClocks;
	private final IntMatrix matrix;

	////

	SimpleDBM(final int size, final IntBinaryOperator values) {
		checkArgument(size > 0);
		this.nClocks = size - 1;
		matrix = IntMatrix.create(size, size);
		matrix.fill(values);
	}

	SimpleDBM(final SimpleDBM dbm) {
		this.nClocks = dbm.nClocks;
		this.matrix = IntMatrix.copyOf(dbm.matrix);
	}

	////

	int get(final int x, final int y) {
		checkArgument(isClock(x));
		checkArgument(isClock(y));
		return matrix.get(x, y);
	}

	void set(final int x, final int y, final int b) {
		checkArgument(isClock(x));
		checkArgument(isClock(y));
		matrix.set(x, y, b);
	}

	////

	public static int defaultBound(final int x, final int y) {
		checkArgument(x >= 0);
		checkArgument(y >= 0);

		if (x == 0 || x == y) {
			return Leq(0);
		} else {
			return Inf();
		}
	}

	////

	public int size() {
		return nClocks + 1;
	}

	////

	public boolean isConsistent() {
		return matrix.get(0, 0) >= 0;
	}

	public boolean isSatisfied(final int x, final int y, final int b) {
		checkArgument(isClock(x));
		checkArgument(isClock(y));
		return add(matrix.get(y, x), b) >= 0;
	}

	public boolean constrains(final int x) {
		checkArgument(isClock(x));
		for (int i = 0; i <= nClocks; i++) {
			if (matrix.get(x, i) < defaultBound(x, i)) {
				return true;
			}

			if (matrix.get(i, x) < defaultBound(i, x)) {
				return true;
			}
		}
		return false;
	}

	////

	public void up() {
		for (int i = 1; i <= nClocks; i++) {
			matrix.set(i, 0, Inf());
		}
		assert isClosed();
	}

	public void down() {
		for (int i = 1; i <= nClocks; i++) {
			matrix.set(0, i, Leq(0));
			for (int j = 1; j <= nClocks; j++) {
				if (matrix.get(j, i) < matrix.get(0, i)) {
					matrix.set(0, i, matrix.get(j, i));
				}
			}
		}
		assert isClosed();
	}

	public void and(final int x, final int y, final int b) {
		checkArgument(isClock(x));
		checkArgument(isClock(y));

		if (add(matrix.get(y, x), b) < 0) {
			matrix.set(0, 0, Leq(-1));

		} else if (b < matrix.get(x, y)) {
			matrix.set(x, y, b);

			for (int i = 0; i <= nClocks; i++) {
				for (int j = 0; j <= nClocks; j++) {
					if (add(matrix.get(i, x), matrix.get(x, j)) < matrix.get(i, j)) {
						matrix.set(i, j, add(matrix.get(i, x), matrix.get(x, j)));
					}
					if (add(matrix.get(i, y), matrix.get(y, j)) < matrix.get(i, j)) {
						matrix.set(i, j, add(matrix.get(i, y), matrix.get(y, j)));
					}
				}
			}
		}
		assert !isConsistent() || isClosed();
	}

	public void free(final int x) {
		checkArgument(isNonZeroClock(x));

		for (int i = 0; i <= nClocks; i++) {
			if (i != x) {
				matrix.set(x, i, Inf());
				matrix.set(i, x, matrix.get(i, 0));
			}
		}
		assert isClosed();
	}

	public void reset(final int x, final int m) {
		checkArgument(isNonZeroClock(x));

		for (int i = 0; i <= nClocks; i++) {
			matrix.set(x, i, add(Leq(m), matrix.get(0, i)));
			matrix.set(i, x, add(matrix.get(i, 0), Leq(-m)));
		}
		assert isClosed();
	}

	public void copy(final int x, final int y) {

		checkArgument(isNonZeroClock(y));

		for (int i = 0; i <= nClocks; i++) {
			if (i != x) {
				matrix.set(x, i, matrix.get(y, i));
				matrix.set(i, x, matrix.get(i, y));
			}
		}
		matrix.set(x, y, Leq(0));
		matrix.set(y, x, Leq(0));
		assert isClosed();
	}

	@SuppressWarnings("unused")
	private void shift(final int x, final int m) {
		checkArgument(isNonZeroClock(x));

		for (int i = 0; i <= nClocks; i++) {
			if (i != x) {
				matrix.set(x, i, add(matrix.get(x, i), Leq(m)));
				matrix.set(i, x, add(matrix.get(i, x), Leq(-m)));
			}
		}
		matrix.set(x, 0, max(matrix.get(x, 0), Leq(0)));
		matrix.set(0, x, min(matrix.get(0, x), Leq(0)));
		assert isClosed();
	}

	////

	@SuppressWarnings("unused")
	private void norm(final int[] k) {
		for (int i = 0; i <= nClocks; i++) {
			for (int j = 0; j <= nClocks; j++) {
				if (matrix.get(i, j) != Inf()) {
					if (matrix.get(i, j) > Leq(k[i])) {
						matrix.set(i, j, Inf());
					} else if (matrix.get(i, j) < Leq(-k[j])) {
						matrix.set(i, j, Lt(-k[j]));
					}
				}
			}
		}
		close();
	}

	private void close() {
		for (int k = 0; k <= nClocks; k++) {
			for (int i = 0; i <= nClocks; i++) {
				for (int j = 0; j <= nClocks; j++) {
					matrix.set(i, j, min(matrix.get(i, j), add(matrix.get(i, k), matrix.get(k, j))));
				}
			}
		}
		assert isClosed();
	}

	private boolean isClosed() {
		for (int i = 0; i <= nClocks; i++) {
			for (int j = 0; j <= nClocks; j++) {
				for (int k = 0; k <= nClocks; k++) {
					if (matrix.get(i, j) > add(matrix.get(i, k), matrix.get(k, j))) {
						return false;
					}
				}
			}
		}
		return true;
	}

	////

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (int i = 0; i <= nClocks; i++) {
			for (int j = 0; j <= nClocks; j++) {
				sb.append(String.format("%-12s", asString(matrix.get(i, j))));
			}
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}

	////

	private boolean isClock(final int x) {
		return x >= 0 && x <= nClocks;
	}

	private boolean isNonZeroClock(final int x) {
		return x >= 1 && x <= nClocks;
	}

}
