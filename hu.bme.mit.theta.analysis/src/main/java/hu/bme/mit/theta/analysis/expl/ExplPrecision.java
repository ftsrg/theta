package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
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

public final class ExplPrecision implements Precision {

	private final Set<VarDecl<?>> vars;

	private ExplPrecision(final Iterable<? extends VarDecl<?>> vars) {
		checkNotNull(vars);
		this.vars = ImmutableSet.copyOf(vars);
	}

	public static ExplPrecision create(final Iterable<? extends VarDecl<?>> vars) {
		return new ExplPrecision(vars);
	}

	public ExplPrecision refine(final Iterable<? extends VarDecl<?>> newVars) {
		checkNotNull(newVars);
		final Collection<VarDecl<?>> newVisibleVars = ImmutableSet.<VarDecl<?>>builder().addAll(vars).addAll(newVars)
				.build();
		return create(newVisibleVars);
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
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(vars).toString();
	}
}