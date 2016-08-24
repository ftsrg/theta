package hu.bme.mit.inf.theta.program.ui.impl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.theta.core.decl.ConstDecl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.program.ui.ProgramModel;

public final class ProgramModelBuilder {

	private final Collection<ConstDecl<? extends Type>> constDecls;
	private final Collection<Expr<? extends BoolType>> constraints;
	private final Collection<ProcDecl<? extends Type>> procDecls;

	ProgramModelBuilder() {
		constDecls = new ArrayList<>();
		constraints = new HashSet<>();
		procDecls = new ArrayList<>();
	}

	public ProgramModel build() {
		return new ProgramModelImpl(this);
	}

	////////

	public ProgramModelBuilder addConstDecl(final ConstDecl<? extends Type> constDecl) {
		constDecls.add(constDecl);
		return this;
	}

	public ProgramModelBuilder addProcDecl(final ProcDecl<? extends Type> procDecl) {
		procDecls.add(procDecl);
		return this;
	}

	public ProgramModelBuilder addConstraint(final Expr<? extends BoolType> constraint) {
		constraints.add(constraint);
		return this;
	}

	////////

	public Collection<ConstDecl<? extends Type>> getConstDecls() {
		return Collections.unmodifiableCollection(constDecls);
	}

	public Collection<ProcDecl<? extends Type>> getProcDecls() {
		return Collections.unmodifiableCollection(procDecls);
	}

	public Collection<Expr<? extends BoolType>> getConstraints() {
		return Collections.unmodifiableCollection(constraints);
	}

}
