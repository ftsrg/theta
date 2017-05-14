package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class ItpRefToExplPrec implements RefutationToPrec<ExplPrec, ItpRefutation> {

	@Override
	public ExplPrec toPrec(final ItpRefutation refutation, final int index) {
		final Expr<? extends BoolType> expr = refutation.get(index);
		final Collection<VarDecl<? extends Type>> vars = ExprUtils.getVars(expr);
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
