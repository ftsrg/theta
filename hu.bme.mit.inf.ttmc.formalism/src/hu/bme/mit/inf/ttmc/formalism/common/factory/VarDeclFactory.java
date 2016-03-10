package hu.bme.mit.inf.ttmc.formalism.common.factory;

import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public interface VarDeclFactory extends DeclFactory {

	public <T extends Type> VarDecl<T> Var(final String name, final T type);

}
