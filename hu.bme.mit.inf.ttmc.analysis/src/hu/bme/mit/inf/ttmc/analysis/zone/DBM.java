package hu.bme.mit.inf.ttmc.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Lt;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.add;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.asString;
import static java.lang.Math.max;
import static java.lang.Math.min;

import hu.bme.mit.inf.ttmc.common.matrix.IntMatrix;

final class DBM {

	private final int n;
	private final IntMatrix D;

	private DBM(final IntMatrix D) {
		this.n = D.nCols() - 1;
		this.D = D;
	}

	public static DBM zero(final int n) {
		checkArgument(n >= 0);
		final IntMatrix D = IntMatrix.create(n + 1);
		D.fill(Leq(0));
		return new DBM(D);
	}

	public static DBM top(final int n) {
		checkArgument(n >= 0);
		final IntMatrix D = IntMatrix.create(n + 1);
		D.fill(Inf());
		D.set(0, 0, Leq(0));
		for (int i = 1; i < D.nRows(); i++) {
			D.set(0, i, Leq(0));
			D.set(i, i, Leq(0));
		}
		return new DBM(D);
	}

	public static DBM copyOf(final DBM dbm) {
		final IntMatrix D = IntMatrix.copyOf(dbm.D);
		return new DBM(D);
	}

	////////

	public int nClocks() {
		return n;
	}

	public int get(final int x, final int y) {
		checkArgument(isClock(x));
		checkArgument(isClock(y));
		return D.get(x, y);
	}

	////////

	public boolean isConsistent() {
		return D.get(0, 0) >= 0;
	}

	public boolean isSatisfied(final int x, final int y, final int b) {
		checkArgument(isClock(x));
		checkArgument(isClock(y));
		return add(D.get(y, x), b) >= 0;
	}

	////////

	public void up() {
		for (int i = 1; i <= n; i++) {
			D.set(i, 0, Inf());
		}
	}

	public void down() {
		for (int i = 1; i <= n; i++) {
			D.set(0, i, Leq(0));
			for (int j = 1; j <= n; j++) {
				if (D.get(j, i) < D.get(0, i)) {
					D.set(0, i, D.get(j, i));
				}
			}
		}
	}

	public void and(final int x, final int y, final int b) {
		checkArgument(isClock(x));
		checkArgument(isClock(y));

		if (add(D.get(y, x), b) < 0) {
			D.set(0, 0, Leq(-1));

		} else if (b < D.get(x, y)) {
			D.set(x, y, b);

			for (int i = 0; i <= n; i++) {
				for (int j = 0; j <= n; j++) {
					if (add(D.get(i, x), D.get(x, j)) < D.get(i, j)) {
						D.set(i, j, add(D.get(i, x), D.get(x, j)));
					}
					if (add(D.get(i, y), D.get(y, j)) < D.get(i, j)) {
						D.set(i, j, add(D.get(i, y), D.get(y, j)));
					}
				}
			}
		}
	}

	public void free(final int x) {
		checkArgument(isNonZeroClock(x));

		for (int i = 0; i <= n; i++) {
			if (i != x) {
				D.set(x, i, Inf());
				D.set(i, x, D.get(i, 0));
			}
		}
	}

	public void reset(final int x, final int m) {
		checkArgument(isNonZeroClock(x));
		for (int i = 0; i <= n; i++) {
			D.set(x, i, add(Leq(m), D.get(0, i)));
			D.set(i, x, add(D.get(i, 0), Leq(-m)));
		}
	}

	public void copy(final int x, final int y) {
		checkArgument(isNonZeroClock(x));
		checkArgument(isNonZeroClock(y));

		for (int i = 0; i <= n; i++) {
			if (i != x) {
				D.set(x, i, D.get(y, i));
				D.set(i, x, D.get(i, y));
			}
		}
		D.set(x, y, Leq(0));
		D.set(y, x, Leq(0));
	}

	public void shift(final int x, final int m) {
		checkArgument(isNonZeroClock(x));

		for (int i = 0; i <= n; i++) {
			if (i != x) {
				D.set(x, i, add(D.get(x, i), Leq(m)));
				D.set(i, x, add(D.get(i, x), Leq(-m)));
			}
		}
		D.set(x, 0, max(D.get(x, 0), Leq(0)));
		D.set(0, x, min(D.get(0, x), Leq(0)));
	}

	public void norm(final int[] k) {
		checkArgument(k.length == n + 1);

		for (int i = 0; i <= n; i++) {
			for (int j = 0; j <= n; j++) {
				if (D.get(i, j) != Inf()) {
					if (D.get(i, j) > Leq(k[i])) {
						D.set(i, j, Inf());
					} else if (D.get(i, j) < Leq(-k[j])) {
						D.set(i, j, Lt(-k[j]));
					}
				}
			}
		}
		close();
	}

	////////

	private void close() {
		for (int k = 0; k <= n; k++) {
			for (int i = 0; i <= n; i++) {
				for (int j = 0; j <= n; j++) {
					D.set(i, j, min(D.get(i, j), add(D.get(i, k), D.get(k, j))));
				}
			}
		}
	}

	////////

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (int i = 0; i <= n; i++) {
			for (int j = 0; j <= n; j++) {
				if (j < n) {
					sb.append(String.format("%-12s", asString(D.get(i, j))));
				} else {
					sb.append(asString(D.get(i, n)));
					if (i < n) {
						sb.append(System.lineSeparator());
					}
				}
			}

		}
		return sb.toString();
	}

	////////

	private boolean isNonZeroClock(final int x) {
		return x >= 1 && x <= n;
	}

	private boolean isClock(final int x) {
		return x >= 0 && x <= n;
	}

}
