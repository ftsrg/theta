/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *  
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *  
 *      http://www.apache.org/licenses/LICENSE-2.0
 *  
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkPositionIndex;
import static java.lang.Math.abs;
import static java.lang.Math.log10;
import static java.lang.Math.max;

import java.util.Arrays;
import java.util.function.IntBinaryOperator;

public final class IntMatrix {

	private int nRows;
	private int nCols;
	private int[] matrix;

	private int actualSize;

	private IntMatrix(final int nRows, final int nCols) {
		checkArgument(nRows > 0);
		checkArgument(nCols > 0);
		this.nRows = nRows;
		this.nCols = nCols;
		actualSize = matrixSizeFor(nRows, nCols);
		matrix = new int[actualSize * actualSize];
	}

	private IntMatrix(final int[] matrix, final int nCols, final int nRows) {
		this.nRows = nRows;
		this.nCols = nCols;
		actualSize = matrixSizeFor(nRows, nCols);
		this.matrix = Arrays.copyOf(matrix, actualSize * actualSize);
	}

	public static IntMatrix create(final int nRows, final int nCols) {
		return new IntMatrix(nCols, nRows);
	}

	public static IntMatrix copyOf(final IntMatrix other) {
		return new IntMatrix(other.matrix, other.nCols, other.nRows);
	}

	////

	public int get(final int row, final int col) {
		checkPositionIndex(row, nRows);
		checkPositionIndex(col, nCols);
		return matrix[index(row, col)];
	}

	public void set(final int row, final int col, final int value) {
		checkPositionIndex(row, nRows);
		checkPositionIndex(col, nCols);
		matrix[index(row, col)] = value;
	}

	////

	public void fill(final int value) {
		for (int i = 0; i < nRows; i++) {
			for (int j = 0; j < nCols; j++) {
				set(i, j, value);
			}
		}
	}

	public void fill(final IntBinaryOperator op) {
		for (int i = 0; i < nRows; i++) {
			for (int j = 0; j < nCols; j++) {
				set(i, j, op.applyAsInt(i, j));
			}
		}
	}

	////

	public int getNRows() {
		return nRows;
	}

	public int getNCols() {
		return nCols;
	}

	////

	public void expand(final int rows, final int cols) {
		checkArgument(rows >= this.nRows);
		checkArgument(cols >= this.nCols);

		this.nRows = rows;
		this.nCols = cols;

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
		final int maxLength = maxNDigits();
		for (int i = 0; i < nRows; i++) {
			for (int j = 0; j < nCols; j++) {
				if (j < nCols - 1) {
					sb.append(String.format("%" + Integer.toString(-maxLength - 1) + "s", get(i, j)));
				} else {
					sb.append(get(i, j));
					if (i < getNRows() - 1) {
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

	private int maxNDigits() {
		int result = 0;
		for (int i = 0; i < getNRows(); i++) {
			for (int j = 0; j < getNCols(); j++) {
				result = max(result, nDigits(get(i, j)));
			}
		}
		return result;
	}

	private static int nDigits(final int n) {
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
