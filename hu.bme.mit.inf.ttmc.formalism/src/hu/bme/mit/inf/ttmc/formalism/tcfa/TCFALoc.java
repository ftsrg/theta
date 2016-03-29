package hu.bme.mit.inf.ttmc.formalism.tcfa;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Loc;

public interface TCFALoc extends Loc {

	public boolean isUrgent();

	public Expr<? extends BoolType> getInvar();

	@Override
	public Collection<? extends TCFAEdge> getInEdges();

	@Override
	public Collection<? extends TCFAEdge> getOutEdges();

}