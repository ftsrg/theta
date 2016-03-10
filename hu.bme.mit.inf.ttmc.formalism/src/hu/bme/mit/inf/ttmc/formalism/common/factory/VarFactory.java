package hu.bme.mit.inf.ttmc.formalism.common.factory;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public interface VarFactory {

	public <T extends Type> VarDecl<T> Var(final String name, final T type);

}
