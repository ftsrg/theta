package hu.bme.mit.theta.analysis.sts;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Prime;
import static hu.bme.mit.theta.core.utils.impl.VarIndexing.all;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.formalism.sts.STS;

public final class StsAction implements ExprAction {

	private final Expr<? extends BoolType> trans;
	private final Expr<? extends BoolType> invar;
	private final Expr<? extends BoolType> expr;

	StsAction(final STS sts) {
		checkNotNull(sts);
		this.trans = And(sts.getTrans());
		this.invar = And(sts.getInvar());
		this.expr = And(this.invar, this.trans, Prime(this.invar));
	}

	public Expr<? extends BoolType> getTrans() {
		return trans;
	}

	public Expr<? extends BoolType> getInvar() {
		return invar;
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		return expr;
	}

	@Override
	public VarIndexing nextIndexing() {
		return all(1);
	}

	@Override
	public String toString() {
		return expr.toString();
	}
}
