package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.expr.refinement.VarsRefutation;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.VarDecl;

public class VarsRefToExplPrec implements RefutationToPrec<ExplPrec, VarsRefutation> {

	@Override
	public ExplPrec toPrec(final VarsRefutation refutation, final int index) {
		final Collection<VarDecl<? extends Type>> vars = refutation.getVarSets().getVars(index);
		final ExplPrec prec = ExplPrec.create(vars);
		return prec;
	}

	@Override
	public ExplPrec join(final ExplPrec prec1, final ExplPrec prec2) {
		checkNotNull(prec1);
		checkNotNull(prec2);
		return prec1.join(prec2);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
