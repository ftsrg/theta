package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.common.dsl.Symbol;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

final class TcfaLocSymbol implements Symbol {

	private final TCFALoc loc;

	public TcfaLocSymbol(final TCFALoc loc) {
		this.loc = checkNotNull(loc);
	}

	@Override
	public String getName() {
		return loc.getName();
	}

	public TCFALoc geLoc() {
		return loc;
	}

}
