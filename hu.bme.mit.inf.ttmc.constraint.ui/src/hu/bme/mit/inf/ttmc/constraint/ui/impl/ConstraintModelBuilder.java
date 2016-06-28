package hu.bme.mit.inf.ttmc.constraint.ui.impl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.constraint.ui.ConstraintModel;
import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public class ConstraintModelBuilder {

	private final Collection<ConstDecl<? extends Type>> constDecls;
	private final Collection<Expr<? extends BoolType>> constraints;

	ConstraintModelBuilder() {
		constDecls = new ArrayList<>();
		constraints = new HashSet<>();
	}

	////

	public ConstraintModel build() {
		return new ConstraintModelImpl(this);
	}

	////

	public ConstraintModelBuilder addConstDecl(final ConstDecl<? extends Type> constDecl) {
		constDecls.add(constDecl);
		return this;
	}

	public ConstraintModelBuilder addConstDecls(final Collection<ConstDecl<? extends Type>> constDecls) {
		this.constDecls.addAll(constDecls);
		return this;
	}

	public ConstraintModelBuilder addConstraint(final Expr<? extends BoolType> constraint) {
		constraints.add(constraint);
		return this;
	}

	public ConstraintModelBuilder addConstraints(final Collection<Expr<? extends BoolType>> constraints) {
		this.constraints.addAll(constraints);
		return this;
	}

	////

	public Collection<ConstDecl<? extends Type>> getConstDecls() {
		return Collections.unmodifiableCollection(constDecls);
	}

	public Collection<Expr<? extends BoolType>> getConstraints() {
		return Collections.unmodifiableCollection(constraints);
	}

}
