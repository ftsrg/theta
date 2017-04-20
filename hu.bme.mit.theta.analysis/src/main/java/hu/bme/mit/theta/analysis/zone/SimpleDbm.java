package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.Lt;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.add;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.asString;
import static java.lang.Math.min;

import java.util.Arrays;
import java.util.function.IntBinaryOperator;

import hu.bme.mit.theta.common.IntMatrix;

final class SimpleDbm {

	private final int nClocks;
	private final IntMatrix matrix;

	////

	SimpleDbm(final int size, final IntBinaryOperator values) {
		checkArgument(size > 0, "Zero sized DBM");
		checkNotNull(values);
		this.nClocks = size - 1;
		matrix = IntMatrix.create(size, size);
		fill(values);
	}

	SimpleDbm(final SimpleDbm dbm) {
		this.nClocks = dbm.nClocks;
		this.matrix = IntMatrix.copyOf(dbm.matrix);
	}

	////

	public static int defaultBound(final int x, final int y) {
		checkArgument(x >= 0);
		checkArgument(y >= 0);

		if (x == y) {
			return Leq(0);
		} else {
			return Inf();
		}
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

	void fill(final IntBinaryOperator values) {
		checkNotNull(values);
		matrix.fill(values);
	}

	////

	public int size() {
		return nClocks + 1;
	}

	////

	public boolean isConsistent() {
		return matrix.get(0, 0) > 0;
	}

	public boolean isSatisfied(final int x, final int y, final int b) {
		checkArgument(isClock(x));
		checkArgument(isClock(y));
		return add(matrix.get(y, x), b) >= Leq(0);
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
		if (isConsistent()) {
			for (int i = 1; i <= nClocks; i++) {
				matrix.set(i, 0, Inf());
			}
			assert isClosed();
		}
	}

	public void down() {
		if (isConsistent()) {
			for (int i = 1; i <= nClocks; i++) {
				matrix.set(0, i, Inf());
			}
			assert isClosed();
		}
	}

	public void and(final int x, final int y, final int b) {
		checkArgument(isClock(x));
		checkArgument(isClock(y));

		if (!isConsistent()) {
			// do nothing

		} else if (!isSatisfied(x, y, b)) {
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

		if (isConsistent()) {
			for (int i = 0; i <= nClocks; i++) {
				if (i != x) {
					matrix.set(x, i, Inf());
					matrix.set(i, x, Inf());
				}
			}
			assert isClosed();
		}
	}

	public void free() {
		fill(SimpleDbm::defaultBound);
	}

	public void reset(final int x, final int m) {
		checkArgument(isNonZeroClock(x));

		if (isConsistent()) {
			for (int i = 0; i <= nClocks; i++) {
				matrix.set(x, i, add(Leq(m), matrix.get(0, i)));
				matrix.set(i, x, add(matrix.get(i, 0), Leq(-m)));
			}

			assert isClosed();
		}
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

	public void shift(final int x, final int m) {
		checkArgument(isNonZeroClock(x));

		for (int i = 0; i <= nClocks; i++) {
			if (i != x) {
				matrix.set(x, i, add(matrix.get(x, i), Leq(m)));
				matrix.set(i, x, add(matrix.get(i, x), Leq(-m)));
			}
		}
		assert isClosed();
	}

	public void norm(final int[] k) {
		checkNotNull(k);
		checkArgument(k.length == nClocks + 1);

		for (int i = 0; i <= nClocks; i++) {
			for (int j = 0; j <= nClocks; j++) {
				if (matrix.get(i, j) != Inf()) {
					if (matrix.get(i, j) > Leq(k[i])) {
						matrix.set(i, j, Inf());
					} else if (matrix.get(i, j) < Lt(-k[j])) {
						matrix.set(i, j, Lt(-k[j]));
					}
				}
			}
		}
		close();
	}

	void close() {
		for (int k = 0; k <= nClocks; k++) {
			for (int i = 0; i <= nClocks; i++) {
				for (int j = 0; j <= nClocks; j++) {
					final int newBound = min(matrix.get(i, j), add(matrix.get(i, k), matrix.get(k, j)));
					if (i == j && newBound < Leq(0)) {
						matrix.set(0, 0, Leq(-1));
						return;
					} else {
						matrix.set(i, j, newBound);
					}
				}
			}
		}
		assert isClosed();
	}

	int[] closeItp() {
		final IntMatrix next = IntMatrix.create(nClocks + 1, nClocks + 1);
		next.fill((x, y) -> y);

		for (int k = 0; k <= nClocks; k++) {
			for (int i = 0; i <= nClocks; i++) {
				for (int j = 0; j <= nClocks; j++) {
					final int newBound = add(matrix.get(i, k), matrix.get(k, j));
					if (newBound < matrix.get(i, j)) {
						matrix.set(i, j, newBound);
						next.set(i, j, next.get(i, k));
						if (i == j && newBound < Leq(0)) {
							final int[] cycle = path(next, i, j);
							return cycle;
						}
					}
				}
			}
		}

		throw new IllegalStateException();
	}

	private int[] path(final IntMatrix next, final int u, final int v) {
		final int[] path = new int[nClocks + 2];

		int w = u;
		path[0] = w;
		int i = 1;
		do {
			w = next.get(w, v);
			path[i] = w;
			i++;
		} while (w != v);

		return Arrays.copyOf(path, i);
	}

	boolean isClosed() {
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
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean equals(final Object obj) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

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
