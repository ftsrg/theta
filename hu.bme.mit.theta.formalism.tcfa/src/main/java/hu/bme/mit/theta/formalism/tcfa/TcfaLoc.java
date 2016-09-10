package hu.bme.mit.theta.formalism.tcfa;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.common.Loc;

public interface TcfaLoc extends Loc<TcfaLoc, TcfaEdge> {

	public String getName();

	public boolean isUrgent();

	public Collection<Expr<? extends BoolType>> getInvars();

}