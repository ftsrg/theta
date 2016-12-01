package hu.bme.mit.theta.splittingcegar.visible.steps.refinement;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractState;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractSystem;

public interface VarCollector {
	Collection<VarDecl<? extends Type>> collectVars(VisibleAbstractSystem system,
			List<VisibleAbstractState> abstractCounterEx, ConcreteTrace concreteCounterEx);
}
