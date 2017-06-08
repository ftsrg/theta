package hu.bme.mit.theta.splittingcegar.common.data;

import java.util.Set;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.formalism.sts.STS;

/**
 * Common interface for abstract systems.
 */
public interface AbstractSystem {

	STS getSTS();

	Set<VarDecl<?>> getVars();

}
