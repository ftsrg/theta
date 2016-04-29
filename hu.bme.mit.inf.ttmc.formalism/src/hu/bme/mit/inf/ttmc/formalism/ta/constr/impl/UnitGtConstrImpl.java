package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Gt;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Ref;

import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ConstrVisitor;

final class UnitGtConstrImpl extends AbstractUnitConstr implements UnitGtConstr {

	private static final int HASH_SEED = 9161;

	private static final String OPERATOR_LABEL = ">";

	private volatile GtExpr expr = null;

	UnitGtConstrImpl(final Clock clock, final int bound) {
		super(clock, bound);
	}

	@Override
	public GtExpr asExpr() {
		GtExpr result = expr;
		if (result == null) {
			final ClockDecl decl = getClock().asDecl();
			result = Gt(Ref(decl), Int(getBound()));
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
		} else if (obj instanceof UnitGtConstr) {
			final UnitGtConstr that = (UnitGtConstr) obj;
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
