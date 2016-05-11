package hu.bme.mit.inf.ttmc.common.matrix;

import static com.google.common.base.Preconditions.checkArgument;
import static java.lang.Math.abs;
import static java.lang.Math.log10;
import static java.lang.Math.max;

public abstract class IntMatrix {

	IntMatrix() {
	}

	public static IntMatrix create(final int m, final int n) {
		checkArgument(m >= 0);
		checkArgument(n >= 0);
		return new IntMatrixImpl(m, n);
	}

	public static IntMatrix create(final int n) {
		checkArgument(n >= 0);
		return new IntMatrixImpl(n, n);
	}

	public static IntMatrix copyOf(final IntMatrix matrix) {
		final IntMatrix result = create(matrix.nRows(), matrix.nCols());
		for (int i = 0; i < matrix.nRows(); i++) {
			for (int j = 0; j < matrix.nRows(); j++) {
				result.set(i, j, matrix.get(i, j));
			}
		}
		return result;
	}

	////////

	public final void fill(final int e) {
		for (int i = 0; i < nRows(); i++) {
			for (int j = 0; j < nCols(); j++) {
				set(i, j, e);
			}
		}
	}

	public final IntMatrix subMatrix(final boolean[] selRows, final boolean[] selCols) {
		checkArgument(selRows.length == nRows());
		checkArgument(selCols.length == nCols());
		return new IntSubMatrixImpl(this, selRows, selCols);
	}

	@Override
	public final int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final boolean equals(final Object obj) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		final int maxLength = maxLength();
		for (int i = 0; i < nRows(); i++) {
			for (int j = 0; j < nCols(); j++) {
				if (j < nCols() - 1) {
					sb.append(String.format("%" + Integer.toString(-maxLength - 1) + "s", get(i, j)));
				} else {
					sb.append(get(i, j));
					if (i < nRows() - 1) {
						sb.append(System.lineSeparator());
					}
				}
			}
		}
		return sb.toString();
	}

	/////

	public abstract int nRows();

	public abstract int nCols();

	public abstract int get(final int i, final int j);

	public abstract void set(final int i, final int j, final int value);

	/////

	private int maxLength() {
		int result = 0;
		for (int i = 0; i < nRows(); i++) {
			for (int j = 0; j < nCols(); j++) {
				result = max(result, length(get(i, j)));
			}
		}
		return result;
	}

	private static int length(final int n) {
		if (n == 0) {
			return 1;
		} else {
			final int nDigits = (int) (log10(abs(n))) + 1;
			if (n >= 0) {
				return nDigits;
			} else {
				return nDigits + 1;
			}
		}
	}

}
