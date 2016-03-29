package hu.bme.mit.inf.ttmc.cegar.common.data;

import java.util.Set;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

/**
 * Common interface for abstract systems.
 */
public interface AbstractSystem {

	STS getSTS();

	Set<VarDecl<? extends Type>> getVars();

	STSUnroller getUnroller();

	STSManager getManager();

}
