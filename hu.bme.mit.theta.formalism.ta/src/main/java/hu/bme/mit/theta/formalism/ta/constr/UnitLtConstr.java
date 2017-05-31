package hu.bme.mit.theta.formalism.ta.constr;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Lt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.rattype.RatLtExpr;

public final class UnitLtConstr extends UnitConstr {

	private static final int HASH_SEED = 3109;

	private static final String OPERATOR_LABEL = "<";

	private volatile RatLtExpr expr = null;

	UnitLtConstr(final VarDecl<RatType> clock, final int bound) {
		super(clock, bound);
	}

	@Override
	public RatLtExpr toExpr() {
		RatLtExpr result = expr;
		if (result == null) {
			final RefExpr<RatType> ref = getVar().getRef();
			result = Lt(ref, Rat(getBound(), 1));
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
		} else if (obj instanceof UnitLtConstr) {
			final UnitLtConstr that = (UnitLtConstr) obj;
			return this.getBound() == that.getBound() && this.getVar().equals(that.getVar());
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
