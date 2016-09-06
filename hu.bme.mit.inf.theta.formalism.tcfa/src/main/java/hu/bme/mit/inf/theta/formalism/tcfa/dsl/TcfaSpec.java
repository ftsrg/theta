package hu.bme.mit.inf.theta.formalism.tcfa.dsl;

import hu.bme.mit.inf.theta.formalism.tcfa.TCFA;

public interface TcfaSpec {

	public TCFA getTcfa(final String name);

}
