package hu.bme.mit.inf.theta.cegar.common.data;

import java.util.Set;

import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.sts.STS;

/**
 * Common interface for abstract systems.
 */
public interface AbstractSystem {

	STS getSTS();

	Set<VarDecl<? extends Type>> getVars();

}
