package hu.bme.mit.theta.formalism.cfa.utils;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.dsl.CoreDslManager;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;

public class CfaWriter {
	public static void write(final CFA cfa, final OutputStream outStream) throws IOException {
		final BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(outStream));

		bw.write("main process cfa {");
		bw.newLine();

		for (final Decl<?> var : cfa.getVars()) {
			final String varName = var.getName();
			final String varType = var.getType().toString().toLowerCase();
			bw.write(String.format("\tvar %s : %s", varName, varType));
			bw.newLine();
		}

		bw.newLine();

		for (final CfaLoc loc : cfa.getLocs()) {
			final String locName = "L" + loc.getName();
			String locPrefix = "";
			if (loc == cfa.getErrorLoc())
				locPrefix += "error ";
			if (loc == cfa.getInitLoc())
				locPrefix += "init ";
			if (loc == cfa.getFinalLoc())
				locPrefix += "final ";
			bw.write(String.format("\t%sloc %s", locPrefix, locName));
			bw.newLine();
		}

		bw.newLine();

		for (final CfaEdge edge : cfa.getEdges()) {
			final String sourceLoc = "L" + edge.getSource().getName();
			final String targetLoc = "L" + edge.getTarget().getName();
			bw.write(String.format("\t%s -> %s {", sourceLoc, targetLoc));
			bw.newLine();
			for (final Stmt stmt : edge.getStmts()) {
				bw.write(String.format("\t\t%s", writeStmt(stmt)));
				bw.newLine();
			}
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
