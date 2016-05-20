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

	private static final int HASH_SEED = 8581;

	private int n;
	private IntMatrix D;

	private DBM(final int n) {
		checkArgument(n >= 0);
		this.n = n;
		this.D = IntMatrix.create(n + 1, n + 1);
		D.fill(Inf());
		for (int i = 0; i <= n; i++) {
			D.set(i, i, Leq(0));
		}
	}

	private DBM(final IntMatrix D) {
		this.n = D.rows() - 1;
		this.D = D;
	}

	public static DBM zero(final int n) {
		checkArgument(n >= 0);
		final DBM result = new DBM(n);
		result.D.fill(Leq(0));

		assert result.isClosed();
		return result;
	}

	public static DBM top(final int n) {
		checkArgument(n >= 0);
		final DBM result = new DBM(n);
		for (int i = 1; i <= n; i++) {
			result.D.set(0, i, Leq(0));
		}

		assert result.isClosed();
		return result;
	}

	public static DBM bottom() {
		final DBM result = new DBM(0);
		result.D.set(0, 0, Leq(-1));

		assert result.isClosed();
		return result;
	}

	////////

	public static DBM copyOf(final DBM dbm) {
		final IntMatrix D = IntMatrix.copyOf(dbm.D);
		return new DBM(D);
	}

	public void expand() {
		final int n2 = n + 1;
		final IntMatrix D2 = IntMatrix.create(n2 + 1, n2 + 1);

		for (int i = 0; i <= n; i++) {
			for (int j = 0; j <= n; j++) {
				D2.set(i, j, D.get(i, j));
			}
			D2.set(n2, i, Inf());
			D2.set(i, n2, D.get(i, 0));
		}
		D2.set(0, n2, Leq(0));
		D2.set(n2, n2, Leq(0));
		n = n2;
		D = D2;
		assert isClosed();
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
		assert isClosed();
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
		assert isClosed();
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
		assert isClosed();
	}

	public void free(final int x) {
		checkArgument(isNonZeroClock(x));
		for (int i = 0; i <= n; i++) {
			if (i != x) {
				D.set(x, i, Inf());
				D.set(i, x, D.get(i, 0));
			}
		}
		assert isClosed();
	}

	public void reset(final int x, final int m) {
		checkArgument(isNonZeroClock(x));
		for (int i = 0; i <= n; i++) {
			D.set(x, i, add(Leq(m), D.get(0, i)));
			D.set(i, x, add(D.get(i, 0), Leq(-m)));
		}
		assert isClosed();
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
		assert isClosed();
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
		assert isClosed();
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

	@Override
	public int hashCode() {
		int result = HASH_SEED;
		result = 31 * result + D.hashCode();
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DBM) {
			final DBM that = (DBM) obj;
			return this.D.equals(that.D);
		} else {
			return false;
		}
	}

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

	boolean isClosed() {
		for (int i = 0; i <= n; i++) {
			for (int j = 0; j <= n; j++) {
				for (int k = 0; k <= n; k++) {
					if (D.get(i, j) > add(D.get(i, k), D.get(k, j))) {
						return false;
					}
					;
				}
			}
		}
		return true;
	}

	private void close() {
		for (int k = 0; k <= n; k++) {
			for (int i = 0; i <= n; i++) {
				for (int j = 0; j <= n; j++) {
					D.set(i, j, min(D.get(i, j), add(D.get(i, k), D.get(k, j))));
				}
			}
		}
		assert isClosed();
	}

	////////

	private boolean isNonZeroClock(final int x) {
		return x >= 1 && x <= n;
	}

	private boolean isClock(final int x) {
		return x >= 0 && x <= n;
	}

}
