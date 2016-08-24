package hu.bme.mit.inf.theta.program.ui.impl;

import java.util.Collection;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.theta.core.decl.ConstDecl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.program.ui.ProgramModel;

public final class ProgramModelImpl implements ProgramModel {

	private final Collection<ConstDecl<? extends Type>> constDecls;
	private final Collection<Expr<? extends BoolType>> constraints;
	private final Collection<ProcDecl<? extends Type>> procDecls;

	public ProgramModelImpl(final ProgramModelBuilder builder) {
		constDecls = ImmutableList.copyOf(builder.getConstDecls());
		constraints = ImmutableSet.copyOf(builder.getConstraints());
		procDecls = ImmutableList.copyOf(builder.getProcDecls());
	}

	public static ProgramModelBuilder builder() {
		return new ProgramModelBuilder();
	}

	@Override
	public Collection<ConstDecl<? extends Type>> getConstDecls() {
		return constDecls;
	}

	@Override
	public Collection<Expr<? extends BoolType>> getConstraints() {
		return constraints;
	}

	@Override
	public Collection<ProcDecl<? extends Type>> getProcDecls() {
		return procDecls;
	}

}
