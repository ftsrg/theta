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
package hu.bme.mit.theta.xcfa.dsl;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Edge;
import hu.bme.mit.theta.xcfa.XCFA.Loc;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.dsl.CoreDslManager;
import hu.bme.mit.theta.core.stmt.Stmt;

public final class XcfaWriter {

	private XcfaWriter() {
	}

	public static void write(final XCFA xcfa, final OutputStream outStream) throws IOException {
		final BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(outStream));

		bw.write("main process xcfa {");
		bw.newLine();

		for (final Decl<?> var : xcfa.getVars()) {
			final String varName = var.getName();
			final String varType = var.getType().toString().toLowerCase();
			bw.write(String.format("\tvar %s : %s", varName, varType));
			bw.newLine();
		}

		bw.newLine();

		for (final Loc loc : xcfa.getLocs()) {
			final String locName = "L" + loc.getName();
			String locPrefix = "";
			if (loc == xcfa.getErrorLoc()) {
				locPrefix += "error ";
			}
			if (loc == xcfa.getInitLoc()) {
				locPrefix += "init ";
			}
			if (loc == xcfa.getFinalLoc()) {
				locPrefix += "final ";
			}
			bw.write(String.format("\t%sloc %s", locPrefix, locName));
			bw.newLine();
		}

		bw.newLine();

		for (final Edge edge : xcfa.getEdges()) {
			final String sourceLoc = "L" + edge.getSource().getName();
			final String targetLoc = "L" + edge.getTarget().getName();
			bw.write(String.format("\t%s -> %s {", sourceLoc, targetLoc));
			bw.newLine();
			bw.write(String.format("\t\t%s", writeStmt(edge.getStmt())));
			bw.newLine();
			bw.write("\t}");
			bw.newLine();
		}

		bw.write("}");
		bw.close();
	}

	private static String writeStmt(final Stmt stmt) {
		final CoreDslManager dslManager = new CoreDslManager();
		return dslManager.writeStmt(stmt);
	}
}
