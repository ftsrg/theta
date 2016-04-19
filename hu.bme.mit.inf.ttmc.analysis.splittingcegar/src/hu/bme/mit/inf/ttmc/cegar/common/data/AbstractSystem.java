package hu.bme.mit.inf.ttmc.cegar.common.data;

import java.util.Set;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Common interface for abstract systems.
 */
public interface AbstractSystem {

	STS getSTS();

	Set<VarDecl<? extends Type>> getVars();

}
