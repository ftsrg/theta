package hu.bme.mit.inf.ttmc.analysis.algorithm.impl.old.refiner;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Refiner;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.refutation.ItpRefutation;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismUtils;

public class GlobalExplItpRefiner implements Refiner<ExplState, GlobalExplPrecision, ItpRefutation> {

	private static final GlobalExplItpRefiner INSTANCE;

	static {
		INSTANCE = new GlobalExplItpRefiner();
	}

	private GlobalExplItpRefiner() {

	}

	public static GlobalExplItpRefiner create() {
		return INSTANCE;
	}

	@Override
	public GlobalExplPrecision refine(final GlobalExplPrecision precision, final Counterexample<ExplState> abstractCex,
			final ItpRefutation refutation) {
		final Set<VarDecl<? extends Type>> newVisiblevars = new HashSet<>();
		for (final Expr<? extends BoolType> pred : refutation) {
			FormalismUtils.collectVars(pred, newVisiblevars);
		}
		return precision.refine(newVisiblevars);
	}

}
