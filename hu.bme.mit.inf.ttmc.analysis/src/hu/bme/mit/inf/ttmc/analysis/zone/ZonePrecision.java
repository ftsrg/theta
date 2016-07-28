package hu.bme.mit.inf.ttmc.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Map;

import com.google.common.collect.ImmutableMap;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public final class ZonePrecision implements Precision {

	private final Map<ClockDecl, Integer> ceilings;

	public ZonePrecision(final Map<? extends ClockDecl, ? extends Integer> ceilings) {
		checkNotNull(ceilings);
		this.ceilings = ImmutableMap.copyOf(ceilings);
	}

	public Collection<ClockDecl> getClocks() {
		return ceilings.keySet();
	}

	public Map<ClockDecl, Integer> asMap() {
		return ceilings;
	}

}
