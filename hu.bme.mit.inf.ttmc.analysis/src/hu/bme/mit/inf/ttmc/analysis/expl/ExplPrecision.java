package hu.bme.mit.inf.ttmc.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class ExplPrecision implements Precision {

	private final Set<VarDecl<? extends Type>> visibleVars;
	private final Set<VarDecl<? extends Type>> invisibleVars;

	public static ExplPrecision create(final Collection<VarDecl<? extends Type>> visibleVars, final Collection<VarDecl<? extends Type>> invisibleVars) {
		return new ExplPrecision(visibleVars, invisibleVars);
	}

	private ExplPrecision(final Collection<VarDecl<? extends Type>> visibleVars, final Collection<VarDecl<? extends Type>> invisibleVars) {
		checkNotNull(visibleVars);
		checkNotNull(invisibleVars);
		this.visibleVars = Collections.unmodifiableSet(new HashSet<>(visibleVars));
		this.invisibleVars = Collections.unmodifiableSet(new HashSet<>(invisibleVars));
	}

	public Collection<VarDecl<? extends Type>> getVisibleVars() {
		return visibleVars;
	}

	public Collection<VarDecl<? extends Type>> getInvisibleVars() {
		return invisibleVars;
	}

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
