package hu.bme.mit.inf.ttmc.common.matrix;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkPositionIndex;

final class IntSubMatrixImpl extends IntMatrix {

	private final IntMatrix matrix;
	private final int[] rowIdxs;
	private final int[] colIdxs;

	IntSubMatrixImpl(final IntMatrix matrix, final boolean[] selRows, final boolean[] selCols) {
		super();
		checkArgument(matrix.nRows() == selRows.length);
		checkArgument(matrix.nCols() == selCols.length);
		this.matrix = matrix;
		rowIdxs = arrayOfIndexes(selRows);
		colIdxs = arrayOfIndexes(selCols);
	}

	////////

	@Override
	public int nRows() {
		return rowIdxs.length;
	}

	@Override
	public int nCols() {
		return colIdxs.length;
	}

	@Override
	public int get(final int i, final int j) {
		checkPositionIndex(i, rowIdxs.length);
		checkPositionIndex(j, colIdxs.length);
		return matrix.get(rowIdxs[i], colIdxs[j]);
	}

	@Override
	public void set(final int i, final int j, final int value) {
		checkPositionIndex(i, rowIdxs.length);
		checkPositionIndex(j, colIdxs.length);
		matrix.set(rowIdxs[i], colIdxs[j], value);
	}

	////

	private static int countTrue(final boolean[] array) {
		int result = 0;
		for (int i = 0; i < array.length; i++) {
			if (array[i]) {
				result++;
			}
		}
		return result;
	}

	private static int[] arrayOfIndexes(final boolean[] array) {
		final int[] result = new int[countTrue(array)];
		int i = 0;
		for (int j = 0; j < array.length; j++) {
			if (array[j]) {
				result[i] = j;
				i++;
			}
		}
		return result;
	}

}
