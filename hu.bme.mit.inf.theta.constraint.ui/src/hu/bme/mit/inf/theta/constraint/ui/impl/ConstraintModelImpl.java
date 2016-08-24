package hu.bme.mit.inf.theta.constraint.ui.impl;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.theta.constraint.ui.ConstraintModel;
import hu.bme.mit.inf.theta.core.decl.ConstDecl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;

public class ConstraintModelImpl implements ConstraintModel {
	private final Collection<ConstDecl<? extends Type>> constDecls;
	private final Collection<Expr<? extends BoolType>> constraints;

	ConstraintModelImpl(final ConstraintModelBuilder builder) {
		this.constDecls = ImmutableList.copyOf(builder.getConstDecls());
		this.constraints = ImmutableList.copyOf(builder.getConstraints());
	}

	public static ConstraintModelBuilder builder() {
		return new ConstraintModelBuilder();
	}

	@Override
	public Collection<ConstDecl<? extends Type>> getConstDecls() {
		return constDecls;
	}

	@Override
	public Collection<Expr<? extends BoolType>> getConstraints() {
		return constraints;
	}
}