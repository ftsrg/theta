package hu.bme.mit.inf.theta.core.model.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.model.Assignment;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;

public class NestedAssignmentImpl implements Assignment {

	private final Assignment enclosingAssignment;
	private final Assignment assignment;

	public NestedAssignmentImpl(final Assignment enclosingAssignment, final Assignment assignment) {
		this.enclosingAssignment = checkNotNull(enclosingAssignment);
		this.assignment = checkNotNull(assignment);
	}

	@Override
	public Collection<? extends Decl<?, ?>> getDecls() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<? extends Expr<DeclType>> eval(
			final Decl<DeclType, DeclKind> decl) {
		final Optional<? extends Expr<DeclType>> optExpr = assignment.eval(decl);
		if (optExpr.isPresent()) {
			return optExpr;
		} else {
			return enclosingAssignment.eval(decl);
		}
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
