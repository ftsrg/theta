package hu.bme.mit.inf.ttmc.formalism.ta;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Loc;

public interface TALoc extends Loc<TALoc, TAEdge> {

	public Collection<Expr<? extends BoolType>> getInvars();

}
