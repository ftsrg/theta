package hu.bme.mit.theta.sts.analysis.utils;

import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.sts.analysis.StsAction;

public final class StsTraceVisualizer {

	private StsTraceVisualizer() {
	}

	public static void printTraceTable(final Trace<Valuation, StsAction> trace, final TableWriter writer) {
		final Set<Decl<?>> allVars = new LinkedHashSet<>();
		for (final Valuation val : trace.getStates()) {
			allVars.addAll(val.getDecls());
		}

		writer.startTable();
		allVars.forEach(v -> writer.cell(v.getName()));
		writer.newRow();
		for (final Valuation val : trace.getStates()) {
			for (final Decl<?> decl : allVars) {
				final Optional<?> eval = val.eval(decl);
				final String evalStr = eval.isPresent() ? eval.get().toString() : "";
				writer.cell(evalStr);
			}
			writer.newRow();
		}
		writer.endTable();
	}

}
