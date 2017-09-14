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
package hu.bme.mit.theta.common.table.impl;

import java.io.PrintStream;

import hu.bme.mit.theta.common.table.TableWriter;

/**
 * Table writer that prints tables to a PrintStream in LaTeX format.
 */
public final class LatexTableWriter implements TableWriter {

	private final PrintStream stream;
	private boolean isFirstCell = true;

	public LatexTableWriter(final PrintStream stream) {
		this.stream = stream;
	}

	public LatexTableWriter() {
		this(System.out);
	}

	@Override
	public TableWriter cell(final Object obj, final int colspan) {
		final String text = obj.toString().replace("_", "\\_").replace("#", "\\#").replace("%", "\\%");
		if (!isFirstCell)
			stream.print(" & ");
		if (colspan != 1)
			stream.print("\\multicolumn{" + colspan + "}{c}{" + text + "}");
		else
			stream.print(text);
		isFirstCell = false;
		return this;
	}

	@Override
	public TableWriter newRow() {
		stream.println("\\\\\\hline");
		isFirstCell = true;
		return this;
	}

}
