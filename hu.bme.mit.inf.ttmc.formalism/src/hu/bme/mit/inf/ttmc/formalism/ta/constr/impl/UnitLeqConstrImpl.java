package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;

import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ConstrVisitor;

final class UnitLeqConstrImpl extends AbstractUnitConstr implements UnitLeqConstr {

	private static final int HASH_SEED = 6653;

	private static final String OPERATOR_LABEL = "<=";

	private volatile LeqExpr expr = null;

	UnitLeqConstrImpl(final ClockDecl clock, final int bound) {
		super(clock, bound);
	}

	@Override
	public LeqExpr asExpr() {
		LeqExpr result = expr;
		if (result == null) {
			final ClockRefExpr ref = getClock().getRef();
			result = Leq(ref, Int(getBound()));
			expr = result;
		}
		return result;
	}

	@Override
	public <P, R> R accept(final ConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof UnitLeqConstr) {
			final UnitLeqConstr that = (UnitLeqConstr) obj;
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
