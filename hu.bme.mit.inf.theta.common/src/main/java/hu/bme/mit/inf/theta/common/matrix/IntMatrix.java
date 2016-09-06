package hu.bme.mit.inf.theta.common.matrix;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkPositionIndex;
import static java.lang.Math.abs;
import static java.lang.Math.log10;
import static java.lang.Math.max;

import java.util.Arrays;
import java.util.function.IntBinaryOperator;

public final class IntMatrix {

	private int rows;
	private int cols;
	private int[] matrix;

	private int actualSize;

	private IntMatrix(final int rows, final int cols) {
		checkArgument(rows > 0);
		checkArgument(cols > 0);
		this.rows = rows;
		this.cols = cols;
		actualSize = matrixSizeFor(rows, cols);
		matrix = new int[actualSize * actualSize];
	}

	private IntMatrix(final int[] matrix, final int cols, final int rows) {
		this.rows = rows;
		this.cols = cols;
		actualSize = matrixSizeFor(rows, cols);
		this.matrix = Arrays.copyOf(matrix, actualSize * actualSize);
	}

	public static IntMatrix create(final int rows, final int cols) {
		return new IntMatrix(cols, rows);
	}

	public static IntMatrix copyOf(final IntMatrix other) {
		return new IntMatrix(other.matrix, other.cols, other.rows);
	}

	////

	public int get(final int row, final int col) {
		checkPositionIndex(row, rows);
		checkPositionIndex(col, cols);
		return matrix[index(row, col)];
	}

	public void set(final int row, final int col, final int value) {
		checkPositionIndex(row, rows);
		checkPositionIndex(col, cols);
		matrix[index(row, col)] = value;
	}

	////

	public void fill(final int value) {
		for (int i = 0; i < rows; i++) {
			for (int j = 0; j < cols; j++) {
				set(i, j, value);
			}
		}
	}

	public void fill(final IntBinaryOperator op) {
		for (int i = 0; i < rows; i++) {
			for (int j = 0; j < cols; j++) {
				set(i, j, op.applyAsInt(i, j));
			}
		}
	}

	////

	public int rows() {
		return rows;
	}

	public int cols() {
		return cols;
	}

	////

	public void expand(final int rows, final int cols) {
		checkArgument(rows >= this.rows);
		checkArgument(cols >= this.cols);

		this.rows = rows;
		this.cols = cols;

		final int minSize = max(rows, cols);
		if (minSize > actualSize) {
			actualSize = max((actualSize * 3) / 2 + 1, minSize);
			matrix = Arrays.copyOf(matrix, actualSize * actualSize);
		}
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
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		final int maxLength = maxLength();
		for (int i = 0; i < rows; i++) {
			for (int j = 0; j < cols; j++) {
				if (j < cols - 1) {
					sb.append(String.format("%" + Integer.toString(-maxLength - 1) + "s", get(i, j)));
				} else {
					sb.append(get(i, j));
					if (i < rows() - 1) {
						sb.append(System.lineSeparator());
					}
				}
			}
		}
		return sb.toString();
	}

	////////

	static int index(final int row, final int col) {
		return row <= col ? col * (col + 1) + row : row * row + col;
	}

	private static int matrixSizeFor(final int rows, final int cols) {
		return max(max(rows, cols), 5);
	}

	////////

	private int maxLength() {
		int result = 0;
		for (int i = 0; i < rows(); i++) {
			for (int j = 0; j < cols(); j++) {
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
