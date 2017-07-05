package hu.bme.mit.theta.core.model;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public class NestedSubstitution implements Substitution {

	private final Substitution enclosingAssignment;
	private final Substitution assignment;

	private NestedSubstitution(final Substitution enclosingAssignment, final Substitution assignment) {
		this.enclosingAssignment = checkNotNull(enclosingAssignment);
		this.assignment = checkNotNull(assignment);
	}

	public static NestedSubstitution create(final Substitution enclosingAssignment, final Substitution assignment) {
		return new NestedSubstitution(enclosingAssignment, assignment);
	}

	////

	@Override
	public Collection<? extends Decl<?>> getDecls() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl) {
		final Optional<? extends Expr<DeclType>> optExpr = assignment.eval(decl);
		if (optExpr.isPresent()) {
			return optExpr;
		} else {
			return enclosingAssignment.eval(decl);
		}
	}

	@Override
	public Expr<BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
