package hu.bme.mit.theta.formalism.ta.constr;

import static hu.bme.mit.theta.core.expr.Exprs.Gt;
import static hu.bme.mit.theta.core.expr.Exprs.Int;
import static hu.bme.mit.theta.core.expr.Exprs.Sub;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.RatType;

public final class DiffGtConstr extends DiffConstr {

	private static final int HASH_SEED = 1493;

	private static final String OPERATOR_LABEL = ">";

	private volatile GtExpr expr = null;

	DiffGtConstr(final VarDecl<RatType> leftVar, final VarDecl<RatType> rightVar, final int bound) {
		super(leftVar, rightVar, bound);
	}

	@Override
	public GtExpr toExpr() {
		GtExpr result = expr;
		if (result == null) {
			final RefExpr<RatType> leftRef = getLeftVar().getRef();
			final RefExpr<RatType> rightRef = getRightVar().getRef();
			result = Gt(Sub(leftRef, rightRef), Int(getBound()));
			expr = result;
		}
		return result;
	}

	@Override
	public <P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DiffGtConstr) {
			final DiffGtConstr that = (DiffGtConstr) obj;
			return this.getBound() == that.getBound() && this.getLeftVar().equals(that.getLeftVar())
					&& this.getRightVar().equals(that.getRightVar());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
