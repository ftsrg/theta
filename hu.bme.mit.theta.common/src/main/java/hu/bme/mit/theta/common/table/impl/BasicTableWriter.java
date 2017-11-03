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
 * A simple table writer that prints tables to a PrintStream using an arbitrary
 * delimeter and a cell pre/postfix.
 *
 * For exemple in ordinary CSV files, the delimeter is ',' and the pre/postfix
 * is '"'.
 */
public final class BasicTableWriter implements TableWriter {

	private final PrintStream stream;
	private final String delimeter;
	private final String prefix;
	private final String postfix;
	private boolean isFirstCell = true;

	public BasicTableWriter(final PrintStream stream, final String delimeter, final String prefix,
			final String postfix) {
		this.stream = stream;
		this.delimeter = delimeter;
		this.prefix = prefix;
		this.postfix = postfix;
	}

	public BasicTableWriter(final PrintStream stream, final String delimeter) {
		this(stream, delimeter, "", "");
	}

	public BasicTableWriter(final PrintStream stream) {
		this(stream, ",");
	}

	public BasicTableWriter() {
		this(System.out);
	}

	@Override
	public TableWriter cell(final Object obj, final int colspan) {
		if (!isFirstCell) {
			stream.print(delimeter);
		}
		stream.print(prefix);
		stream.print(obj);
		stream.print(postfix);
		for (int i = 0; i < colspan - 1; ++i) {
			stream.print(delimeter);
		}
		isFirstCell = false;
		return this;
	}

	@Override
	public TableWriter newRow() {
		stream.println();
		isFirstCell = true;
		return this;
	}

	@Override
	public TableWriter startTable() {
		return this;
	}

	@Override
	public TableWriter endTable() {
		return this;
	}

}
