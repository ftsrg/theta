package hu.bme.mit.theta.formalism.common.decl.impl;

import hu.bme.mit.theta.formalism.common.decl.ClockDecl;

public final class Decls2 {

	private Decls2() {
	}

	public static ClockDecl Clock(final String name) {
		return new ClockDeclImpl(name);
	}

}
