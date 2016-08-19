
package hu.bme.mit.inf.ttmc.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface Model extends Assignment {

	@Override
	Collection<? extends ConstDecl<?>> getDecls();

	@Override
	<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<LitExpr<DeclType>> eval(
			final Decl<DeclType, DeclKind> decl);

}
