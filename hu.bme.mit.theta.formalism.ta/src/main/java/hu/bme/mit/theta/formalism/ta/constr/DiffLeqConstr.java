package hu.bme.mit.theta.formalism.ta.constr;

import static hu.bme.mit.theta.core.expr.Exprs.Int;
import static hu.bme.mit.theta.core.expr.Exprs.Leq;
import static hu.bme.mit.theta.core.expr.Exprs.Sub;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.RatType;

public final class DiffLeqConstr extends DiffConstr {

	private static final int HASH_SEED = 7019;

	private static final String OPERATOR_LABEL = "<=";

	private volatile LeqExpr expr = null;

	DiffLeqConstr(final VarDecl<RatType> leftVar, final VarDecl<RatType> rightVar, final int bound) {
		super(leftVar, rightVar, bound);
	}

	@Override
	public LeqExpr toExpr() {
		LeqExpr result = expr;
		if (result == null) {
			final VarRefExpr<RatType> leftRef = getLeftVar().getRef();
			final VarRefExpr<RatType> rightRef = getRightVar().getRef();
			result = Leq(Sub(leftRef, rightRef), Int(getBound()));
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
		} else if (obj instanceof DiffLeqConstr) {
			final DiffLeqConstr that = (DiffLeqConstr) obj;
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
