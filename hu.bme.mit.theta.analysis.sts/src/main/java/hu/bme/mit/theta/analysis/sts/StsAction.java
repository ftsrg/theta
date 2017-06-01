package hu.bme.mit.theta.analysis.sts;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.VarIndexing.all;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.formalism.sts.STS;

/**
 * Represents an action for an STS, which is simply the transition relation.
 */
public final class StsAction implements ExprAction {

	private final Expr<BoolType> trans;

	StsAction(final STS sts) {
		checkNotNull(sts);
		this.trans = sts.getTrans();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return trans;
	}

	@Override
	public VarIndexing nextIndexing() {
		return all(1);
	}

	@Override
	public String toString() {
		return trans.toString();
	}
}
