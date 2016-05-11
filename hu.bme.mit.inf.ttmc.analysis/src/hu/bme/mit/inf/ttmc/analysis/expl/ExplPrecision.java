package hu.bme.mit.inf.ttmc.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.core.type.Type;
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
}
