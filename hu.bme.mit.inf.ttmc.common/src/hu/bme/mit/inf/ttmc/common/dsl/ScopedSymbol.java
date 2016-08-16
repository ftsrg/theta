package hu.bme.mit.inf.ttmc.common.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public abstract class ScopedSymbol extends BasicScope implements Symbol {

	private final String name;

	public ScopedSymbol(final String name, final Scope eclosingScope) {
		super(eclosingScope);
		checkNotNull(name);
		checkArgument(name.length() > 0);
		this.name = name;
	}

	@Override
	public String getName() {
		return name;
	}

}
