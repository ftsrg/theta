package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public interface VarCollector {
	Collection<VarDecl<? extends Type>> collectVars(VisibleAbstractSystem system, List<VisibleAbstractState> abstractCounterEx,
			ConcreteTrace concreteCounterEx);
}
