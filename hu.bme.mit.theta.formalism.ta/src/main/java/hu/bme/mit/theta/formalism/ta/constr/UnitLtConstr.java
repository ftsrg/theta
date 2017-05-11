package hu.bme.mit.theta.formalism.ta.constr;

import static hu.bme.mit.theta.core.expr.Exprs.Int;
import static hu.bme.mit.theta.core.expr.Exprs.Lt;

import hu.bme.mit.theta.core.expr.LtExpr;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.expr.ClockRefExpr;
import hu.bme.mit.theta.formalism.ta.utils.ClockConstrVisitor;

public final class UnitLtConstr extends UnitConstr {

	private static final int HASH_SEED = 3109;

	private static final String OPERATOR_LABEL = "<";

	private volatile LtExpr expr = null;

	UnitLtConstr(final ClockDecl clock, final int bound) {
		super(clock, bound);
	}

	@Override
	public LtExpr toExpr() {
		LtExpr result = expr;
		if (result == null) {
			final ClockRefExpr ref = getClock().getRef();
			result = Lt(ref, Int(getBound()));
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
			return this.getBound() == that.getBound() && this.getClock().equals(that.getClock());
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
