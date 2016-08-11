package hu.bme.mit.inf.ttmc.common.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

public final class LocalScope extends BasicScope {

	public LocalScope(final Scope enclosingScope) {
		super(checkNotNull(enclosingScope));
	}

}
