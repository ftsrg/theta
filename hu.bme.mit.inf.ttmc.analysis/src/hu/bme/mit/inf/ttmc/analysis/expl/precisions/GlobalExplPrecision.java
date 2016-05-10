package hu.bme.mit.inf.ttmc.analysis.expl.precisions;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class GlobalExplPrecision implements ExplPrecision {

	private final Set<VarDecl<? extends Type>> visibleVars;
	@SuppressWarnings("unused") // It will be used at refinement
	private final Set<VarDecl<? extends Type>> invisibleVars;

	public static GlobalExplPrecision create(final Collection<VarDecl<? extends Type>> visibleVars, final Collection<VarDecl<? extends Type>> invisibleVars) {
		return new GlobalExplPrecision(visibleVars, invisibleVars);
	}

	private GlobalExplPrecision(final Collection<VarDecl<? extends Type>> visibleVars, final Collection<VarDecl<? extends Type>> invisibleVars) {
		checkNotNull(visibleVars);
		checkNotNull(invisibleVars);
		this.visibleVars = Collections.unmodifiableSet(new HashSet<>(visibleVars));
		this.invisibleVars = Collections.unmodifiableSet(new HashSet<>(invisibleVars));
	}

	@Override
	public ExplState mapToAbstractState(final Valuation valuation) {
		checkNotNull(valuation);
		final Valuation.Builder builder = new Valuation.Builder();
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
}
