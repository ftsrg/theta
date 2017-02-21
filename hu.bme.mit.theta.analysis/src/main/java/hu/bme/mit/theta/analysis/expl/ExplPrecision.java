package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.Optional;
import java.util.Set;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.solver.Solver;

/**
 * Represents an immutable, simple explicit precision that is a set of
 * variables.
 */
public final class ExplPrecision implements Precision {

	private final Set<VarDecl<?>> vars;
	private static ExplPrecision EMPTY = new ExplPrecision(Collections.emptySet());

	private ExplPrecision(final Iterable<? extends VarDecl<?>> vars) {
		checkNotNull(vars);
		this.vars = ImmutableSet.copyOf(vars);
	}

	public static ExplPrecision create() {
		return create(Collections.emptySet());
	}

	public static ExplPrecision create(final Iterable<? extends VarDecl<?>> vars) {
		if (vars.iterator().hasNext()) {
			return new ExplPrecision(vars);
		} else {
			return EMPTY;
		}
	}

	public ExplPrecision refine(final Iterable<? extends VarDecl<?>> extraVars) {
		checkNotNull(extraVars);
		final Collection<VarDecl<?>> newVars = ImmutableSet.<VarDecl<?>>builder().addAll(vars).addAll(extraVars)
				.build();
		// If no new variable was added, return same instance (immutable)
		if (newVars.size() == this.vars.size()) {
			return this;
		} else {
			return create(newVars);
		}
	}

	public ExplPrecision refine(final VarDecl<?> extraVar) {
		checkNotNull(extraVar);
		return refine(Collections.singleton(extraVar));
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

	public Collection<ExplState> createStates(final Solver solver, final Expr<? extends BoolType> expr) {
		checkNotNull(solver);
		checkNotNull(expr);
		return ExprStates.createStates(solver, expr, this::createState);
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(vars, VarDecl::getName).toString();
	}
}