package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl;

import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;

public interface TcfaSpec {

	public TCFA getTcfa(final String name);

}
