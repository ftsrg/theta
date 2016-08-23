package hu.bme.mit.inf.ttmc.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;
import java.util.StringJoiner;

import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class GlobalExplPrecision implements ExplPrecision {

	private final Set<VarDecl<? extends Type>> visibleVars;

	public static GlobalExplPrecision create(final Collection<? extends VarDecl<?>> visibleVars) {
		return new GlobalExplPrecision(visibleVars);
	}

	private GlobalExplPrecision(final Collection<? extends VarDecl<?>> visibleVars) {
		checkNotNull(visibleVars);
		this.visibleVars = Collections.unmodifiableSet(new HashSet<>(visibleVars));
	}

	@Override
	public ExplState mapToAbstractState(final Valuation valuation) {
		checkNotNull(valuation);
		final Valuation.Builder builder = Valuation.builder();
		for (final VarDecl<? extends Type> visibleVar : visibleVars) {
			final Optional<? extends LitExpr<? extends Type>> eval = valuation.eval(visibleVar);
			if (eval.isPresent()) {
				builder.put(visibleVar, eval.get());
			} else {
				builder.put(visibleVar, visibleVar.getType().getAny());
			}
		}
		return ExplState.create(builder.build());
	}

	public GlobalExplPrecision refine(final Collection<VarDecl<? extends Type>> makeVisible) {
		checkNotNull(makeVisible);

		final Set<VarDecl<? extends Type>> newVisibleVars = new HashSet<>(visibleVars);

		for (final VarDecl<? extends Type> var : makeVisible) {
			if (newVisibleVars.contains(var)) {
				continue;
			} else {
				newVisibleVars.add(var);
			}
		}

		assert (newVisibleVars.size() >= visibleVars.size());

		return create(newVisibleVars);
	}

	@Override
	public String toString() {
		final String prefix = "GlobalExplPrecision(";
		final String suffix = ")";
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (final VarDecl<? extends Type> var : visibleVars) {
			sj.add(var.toString());
		}
		return sj.toString();
	}
}