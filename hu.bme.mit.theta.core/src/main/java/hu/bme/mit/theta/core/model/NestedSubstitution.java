package hu.bme.mit.theta.core.model;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;

/**
 * Class representing a nested substitution. If a declaration is not present in
 * the actual substitution it is searched in the enclosing substitutions
 * recursively.
 */
public final class NestedSubstitution implements Substitution {

	private final Substitution enclosingSubst;
	private final Substitution subst;

	private NestedSubstitution(final Substitution enclosingSubst, final Substitution subst) {
		this.enclosingSubst = checkNotNull(enclosingSubst);
		this.subst = checkNotNull(subst);
	}

	public static NestedSubstitution create(final Substitution enclosingSubst, final Substitution subst) {
		return new NestedSubstitution(enclosingSubst, subst);
	}

	@Override
	public Collection<? extends Decl<?>> getDecls() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl) {
		final Optional<? extends Expr<DeclType>> optExpr = subst.eval(decl);
		if (optExpr.isPresent()) {
			return optExpr;
		} else {
			return enclosingSubst.eval(decl);
		}
	}
}
