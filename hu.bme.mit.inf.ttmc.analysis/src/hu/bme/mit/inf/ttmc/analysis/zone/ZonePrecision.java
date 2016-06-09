package hu.bme.mit.inf.ttmc.analysis.zone;

import java.util.Collection;

import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public final class ZonePrecision implements Precision {

	private final Collection<ClockDecl> clocks;

	private ZonePrecision(final Builder builder) {
		clocks = builder.clocks.build();
	}

	public static Builder builder() {
		return new Builder();
	}

	public Collection<ClockDecl> getClocks() {
		return clocks;
	}

	////

	public static final class Builder {
		private final ImmutableCollection.Builder<ClockDecl> clocks;

		private Builder() {
			clocks = ImmutableSet.builder();
		}

		public ZonePrecision build() {
			return new ZonePrecision(this);
		}
	}

}
