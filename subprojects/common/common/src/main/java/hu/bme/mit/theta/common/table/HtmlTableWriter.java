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

package hu.bme.mit.theta.common.table;

import java.io.PrintStream;

/**
 * A table writer that prints tables to a PrintStream in HTML format.
 */
public class HtmlTableWriter implements TableWriter {
	private final PrintStream stream;
	private boolean isFirstCell = true;

	public HtmlTableWriter(final PrintStream stream) {
		this.stream = stream;
	}

	@Override
	public TableWriter cell(final Object obj, final int colspan) {
		if (isFirstCell) {
			stream.print("<tr>");
		}
		if (colspan > 1) {
			stream.print("<td colspan=\"" + colspan + "\">");
		} else {
			stream.print("<td>");
		}
		stream.print(obj.toString().replace("\n", "<br />"));
		stream.print("</td>");
		isFirstCell = false;
		return this;
	}

	@Override
	public TableWriter newRow() {
		stream.println("</tr>");
		isFirstCell = true;
		return this;
	}

	@Override
	public TableWriter startTable() {
		stream.println("<table border=\"1\" cellspacing=\"0\">");
		return this;
	}

	@Override
	public TableWriter endTable() {
		stream.println("</table>");
		return this;
	}
}
