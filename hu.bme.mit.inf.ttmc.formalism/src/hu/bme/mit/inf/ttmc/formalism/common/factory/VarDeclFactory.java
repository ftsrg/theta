package hu.bme.mit.inf.ttmc.formalism.common.factory;

import hu.bme.mit.inf.ttmc.core.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public interface VarDeclFactory extends DeclFactory {

	public <T extends Type> VarDecl<T> Var(final String name, final T type);

}
