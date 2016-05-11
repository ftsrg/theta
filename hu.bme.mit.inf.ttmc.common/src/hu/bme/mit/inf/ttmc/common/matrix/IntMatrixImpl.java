package hu.bme.mit.inf.ttmc.common.matrix;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkPositionIndex;

final class IntMatrixImpl extends IntMatrix {

	private final int m;
	private final int n;
	private final int[][] matrix;

	IntMatrixImpl(final int m, final int n) {
		super();
		checkArgument(m >= 0);
		checkArgument(n >= 0);
		this.m = m;
		this.n = n;
		matrix = new int[m][n];
	}

	@Override
	public int nRows() {
		return m;
	}

	@Override
	public int nCols() {
		return n;
	}

	@Override
	public void set(final int i, final int j, final int value) {
		checkPositionIndex(i, m);
		checkPositionIndex(j, n);
		matrix[i][j] = value;
	}

	@Override
	public int get(final int i, final int j) {
		checkPositionIndex(i, m);
		checkPositionIndex(j, n);
		return matrix[i][j];
	}

}
