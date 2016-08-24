package hu.bme.mit.inf.theta.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;

public interface Assignment {

	Collection<? extends Decl<?, ?>> getDecls();

	<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<? extends Expr<DeclType>> eval(
			final Decl<DeclType, DeclKind> decl);

	public Expr<? extends BoolType> toExpr();
}
