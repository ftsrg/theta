package hu.bme.mit.inf.theta.analysis.zone;

import static hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2.Clock;

import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;

class ZeroClock {

	private static final ClockDecl ZERO_CLOCK = Clock("_zero");

	private ZeroClock() {
	}

	static ClockDecl getInstance() {
		return ZERO_CLOCK;
	}

}
