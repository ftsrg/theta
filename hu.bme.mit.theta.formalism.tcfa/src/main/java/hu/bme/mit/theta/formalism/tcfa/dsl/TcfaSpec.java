package hu.bme.mit.theta.formalism.tcfa.dsl;

import hu.bme.mit.theta.formalism.tcfa.TCFA;

public interface TcfaSpec {

	public TCFA getTcfa(final String name);

}
