package hu.bme.mit.inf.ttmc.program.tcfa;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public interface TCFALoc {

	public TCFA getTCFA();

	public boolean isUrgent();

	public Expr<? extends BoolType> getInvar();

	public Collection<? extends TCFAEdge> getInEdges();

	public Collection<? extends TCFAEdge> getOutEdges();

}