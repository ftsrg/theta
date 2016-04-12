package hu.bme.mit.inf.ttmc.core.utils.impl;

import java.util.Collection;
import java.util.Map;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.solver.Model;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public class ModelImpl implements Model {

	@Override
	public <T extends Type> Optional<Expr<T>> eval(ConstDecl<T> decl) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(Expr<T> expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Model with(Map<? extends ConstDecl<?>, ? extends Expr<?>> mapping) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Model without(Collection<? extends ConstDecl<?>> constDecls) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
