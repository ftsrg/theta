package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Lt;

import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ClockConstrVisitor;

final class UnitLtConstrImpl extends AbstractUnitConstr implements UnitLtConstr {

	private static final int HASH_SEED = 3109;

	private static final String OPERATOR_LABEL = "<";

	private volatile LtExpr expr = null;

	UnitLtConstrImpl(final ClockDecl clock, final int bound) {
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
