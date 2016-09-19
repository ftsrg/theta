
package hu.bme.mit.theta.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.Type;

public interface Model extends Assignment {

	@Override
	Collection<? extends ConstDecl<?>> getDecls();

	@Override
	<DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl);

}
