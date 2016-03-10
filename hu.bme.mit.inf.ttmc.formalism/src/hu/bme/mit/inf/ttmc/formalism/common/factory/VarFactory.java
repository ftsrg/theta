package hu.bme.mit.inf.ttmc.formalism.common.factory;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;

public interface VarFactory {

	public <T extends Type> VarDecl<T> Var(final String name, final T type);

	public <T extends Type> VarRefExpr<T> Ref(final VarDecl<T> varDecl);
}
