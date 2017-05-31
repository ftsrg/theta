package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.Optional;
import java.util.Set;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

/**
 * Represents an immutable, simple explicit precision that is a set of
 * variables.
 */
public final class ExplPrec implements Prec {

	private final Set<VarDecl<?>> vars;
	private static ExplPrec EMPTY = new ExplPrec(Collections.emptySet());

	private ExplPrec(final Iterable<? extends VarDecl<?>> vars) {
		this.vars = ImmutableSet.copyOf(vars);
	}

	public static ExplPrec create() {
		return create(Collections.emptySet());
	}

	public static ExplPrec create(final Iterable<? extends VarDecl<?>> vars) {
		checkNotNull(vars);
		if (vars.iterator().hasNext()) {
			return new ExplPrec(vars);
		} else {
			return EMPTY;
		}
	}

	public Set<VarDecl<?>> getVars() {
		return vars;
	}

	public ExplPrec join(final ExplPrec other) {
		checkNotNull(other);
		final Collection<VarDecl<?>> newVars = ImmutableSet.<VarDecl<?>>builder().addAll(vars).addAll(other.vars)
				.build();
		// If no new variable was added, return same instance (immutable)
		if (newVars.size() == this.vars.size()) {
			return this;
		} else if (newVars.size() == other.vars.size()) {
			return other;
		} else {
			return create(newVars);
		}
	}

	public ExplState createState(final Valuation valuation) {
		checkNotNull(valuation);
		final Valuation.Builder builder = Valuation.builder();
		for (final VarDecl<?> var : vars) {
			final Optional<? extends LitExpr<? extends Type>> eval = valuation.eval(var);
			if (eval.isPresent()) {
				builder.put(var, eval.get());
			}
		}
		return ExplState.create(builder.build());
	}

	public Collection<ExplState> createStatesForExpr(final Solver solver, final Expr<? extends BoolType> expr) {
		checkNotNull(solver);
		checkNotNull(expr);
		return ExprStates.createStatesForExpr(solver, expr, this::createState);
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(vars, VarDecl::getName).toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ExplPrec) {
			final ExplPrec that = (ExplPrec) obj;
			return this.getVars().equals(that.getVars());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * vars.hashCode();
	}
}