package hu.bme.mit.theta.formalism.tcfa.dsl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

final class TcfaLocSymbol implements Symbol {

	private final TcfaLoc loc;

	public TcfaLocSymbol(final TcfaLoc loc) {
		this.loc = checkNotNull(loc);
	}

	@Override
	public String getName() {
		return loc.getName();
	}

	public TcfaLoc geLoc() {
		return loc;
	}

}
