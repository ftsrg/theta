package hu.bme.mit.inf.ttmc.analysis.zone;

import java.util.Collection;
import java.util.Set;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public final class ZonePrecision implements Precision {

	private final Set<ClockDecl> clocks;

	private ZonePrecision(final Builder builder) {
		clocks = builder.clocksBuilder.build();
	}

	public static Builder builder() {
		return new Builder();
	}

	public Set<ClockDecl> getClocks() {
		return clocks;
	}

	////

	public static final class Builder {
		private final ImmutableSet.Builder<ClockDecl> clocksBuilder;

		private Builder() {
			clocksBuilder = ImmutableSet.builder();
		}

		public Builder add(final ClockDecl clock) {
			clocksBuilder.add(clock);
			return this;
		}

		public Builder addAll(final Collection<? extends ClockDecl> clocks) {
			clocksBuilder.addAll(clocks);
			return this;
		}

		public ZonePrecision build() {
			return new ZonePrecision(this);
		}
	}

}
