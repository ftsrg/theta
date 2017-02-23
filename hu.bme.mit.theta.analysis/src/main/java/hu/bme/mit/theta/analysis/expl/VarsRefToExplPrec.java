package hu.bme.mit.theta.analysis.expl;

import java.util.Collection;

import hu.bme.mit.theta.analysis.expr.VarsRefutation;
import hu.bme.mit.theta.analysis.expr.RefutationToPrec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public class VarsRefToExplPrec implements RefutationToPrec<ExplPrec, VarsRefutation> {

	@Override
	public ExplPrec toPrec(final VarsRefutation refutation, final int index) {
		final Collection<VarDecl<? extends Type>> vars = refutation.getVarSets().getVars(index);
		final ExplPrec prec = ExplPrec.create(vars);
		return prec;
	}

	@Override
	public ExplPrec join(final ExplPrec prec1, final ExplPrec prec2) {
		return prec1.join(prec2);
	}

}
