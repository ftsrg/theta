package hu.bme.mit.inf.ttmc.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface Assignment {

	Collection<? extends Decl<?, ?>> getDecls();

	<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<LitExpr<DeclType>> eval(final Decl<DeclType, DeclKind> decl);
}
