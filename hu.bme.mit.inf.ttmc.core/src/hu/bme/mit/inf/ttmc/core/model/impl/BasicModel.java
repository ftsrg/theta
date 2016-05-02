package hu.bme.mit.inf.ttmc.core.model.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public final class BasicModel implements Model {

	final Collection<ConstDecl<?>> constDecls;
	final Map<ConstDecl<?>, Expr<?>> constToExpr;

	public BasicModel() {
		this(new HashMap<>());
	}

	public BasicModel(final Map<ConstDecl<?>, Expr<?>> constToExpr) {
		this.constToExpr = new HashMap<ConstDecl<?>, Expr<?>>(constToExpr);
		this.constDecls = ImmutableList.copyOf(constToExpr.keySet());
	}

	@Override
	public Collection<? extends ConstDecl<?>> getConstDecls() {
		return constDecls;
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final ConstDecl<T> decl) {
		checkNotNull(decl);

		if (constToExpr.containsKey(decl)) {

			@SuppressWarnings("unchecked")
			final Expr<T> val = (Expr<T>) constToExpr.get(decl);
			return Optional.of(val);
		}

		return Optional.empty();
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final Expr<T> expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

}
