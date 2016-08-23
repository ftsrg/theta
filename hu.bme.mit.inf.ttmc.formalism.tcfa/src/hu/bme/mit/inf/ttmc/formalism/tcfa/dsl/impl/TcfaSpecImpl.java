package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.TcfaSpec;

final class TcfaSpecImpl implements TcfaSpec {

	private final Map<String, TCFA> stringToTcfa;

	TcfaSpecImpl() {
		stringToTcfa = new HashMap<>();
	}

	@Override
	public TCFA getTcfa(final String name) {
		checkNotNull(name);
		checkArgument(stringToTcfa.containsKey(name));
		return stringToTcfa.get(name);
	}

	public void addTcfa(final String name, final TCFA tcfa) {
		checkNotNull(tcfa);
		checkArgument(!stringToTcfa.containsKey(name));
		stringToTcfa.put(name, tcfa);
	}

}
