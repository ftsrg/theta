package hu.bme.mit.theta.formalism.ta.constr;

import static hu.bme.mit.theta.core.expr.Exprs.False;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.FalseExpr;
import hu.bme.mit.theta.core.type.RatType;

public final class FalseConstr implements ClockConstr {

	private static final int HASH_SEED = 242101;

	private static final String CC_LABEL = "false";

	@Override
	public Collection<VarDecl<RatType>> getVars() {
		return ImmutableSet.of();
	}

	@Override
	public FalseExpr toExpr() {
		return False();
	}

	@Override
	public <P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof FalseConstr;
	}

	@Override
	public String toString() {
		return CC_LABEL;
	}
}
