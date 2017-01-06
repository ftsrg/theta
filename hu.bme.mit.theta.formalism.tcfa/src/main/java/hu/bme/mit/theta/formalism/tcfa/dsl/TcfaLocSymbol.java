package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

final class TcfaLocSymbol implements Symbol {

	private final TcfaLoc loc;

	private TcfaLocSymbol(final TcfaLoc loc) {
		this.loc = checkNotNull(loc);
	}

	public static TcfaLocSymbol of(final TcfaLoc loc) {
		return new TcfaLocSymbol(loc);
	}

	@Override
	public String getName() {
		return loc.getName();
	}

	public TcfaLoc geLoc() {
		return loc;
	}

}
