package hu.bme.mit.inf.ttmc.cegar.common.data;

import java.util.Set;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

/**
 * Common interface for abstract systems.
 *
 * @author Akos
 */
public interface IAbstractSystem {

	STS getSystem();

	Set<VarDecl<? extends Type>> getVariables();

	STSUnroller getUnroller();

}
