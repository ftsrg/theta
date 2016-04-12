package hu.bme.mit.inf.ttmc.solver.impl;

import java.util.Collection;
import java.util.Map;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.solver.Model;

public class ModelImpl implements Model {

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final ConstDecl<T> decl) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final Expr<T> expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Model with(final Map<? extends ConstDecl<?>, ? extends Expr<?>> mapping) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Model without(final Collection<? extends ConstDecl<?>> constDecls) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
