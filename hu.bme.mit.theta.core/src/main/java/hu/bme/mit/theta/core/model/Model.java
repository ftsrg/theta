
package hu.bme.mit.theta.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;

public interface Model extends Assignment {

	@Override
	Collection<? extends ConstDecl<?>> getDecls();

	@Override
	<DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl);

}
