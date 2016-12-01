package hu.bme.mit.theta.formalism.sts.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.formalism.sts.STS;

public final class StsSpec {

	private final Map<String, STS> stringToSts;

	StsSpec() {
		stringToSts = new HashMap<>();
	}

	public Collection<? extends STS> getAllSts() {
		return Collections.unmodifiableCollection(stringToSts.values());
	}

	public STS getSts(final String name) {
		checkNotNull(name);
		checkArgument(stringToSts.containsKey(name));
		return stringToSts.get(name);
	}

	void addSts(final String name, final STS tcfa) {
		checkNotNull(tcfa);
		checkArgument(!stringToSts.containsKey(name));
		stringToSts.put(name, tcfa);
	}

}
