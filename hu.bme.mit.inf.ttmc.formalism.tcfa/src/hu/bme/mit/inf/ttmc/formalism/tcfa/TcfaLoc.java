package hu.bme.mit.inf.ttmc.formalism.tcfa;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.automaton.Loc;

public interface TcfaLoc extends Loc<TcfaLoc, TcfaEdge> {

	public String getName();

	public boolean isUrgent();

	public Collection<Expr<? extends BoolType>> getInvars();

}