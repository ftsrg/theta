package hu.bme.mit.inf.theta.formalism.tcfa;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.common.automaton.Loc;

public interface TcfaLoc extends Loc<TcfaLoc, TcfaEdge> {

	public String getName();

	public boolean isUrgent();

	public Collection<Expr<? extends BoolType>> getInvars();

}