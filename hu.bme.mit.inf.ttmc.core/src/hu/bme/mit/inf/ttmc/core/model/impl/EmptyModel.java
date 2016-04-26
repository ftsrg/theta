package hu.bme.mit.inf.ttmc.core.model.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public class EmptyModel implements Model {

	@Override
	public Collection<? extends ConstDecl<?>> getConstDecls() {
		return Collections.emptySet();
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final ConstDecl<T> decl) {
		return Optional.empty();
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final Expr<T> expr) {
		return Optional.empty();
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

}
