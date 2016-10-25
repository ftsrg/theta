package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Set;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;

public final class ZonePrecision implements Precision {

	private final Set<ClockDecl> clocks;

	private ZonePrecision(final Collection<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		this.clocks = ImmutableSet.copyOf(clocks);
	}

	public static ZonePrecision create(final Collection<? extends ClockDecl> clocks) {
		return new ZonePrecision(clocks);
	}

	public Set<ClockDecl> getClocks() {
		return clocks;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(clocks).toString();
	}
}
