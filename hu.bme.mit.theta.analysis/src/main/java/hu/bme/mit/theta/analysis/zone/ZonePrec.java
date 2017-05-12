package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Set;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

public final class ZonePrec implements Prec {

	private final Set<ClockDecl> clocks;

	private ZonePrec(final Collection<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		this.clocks = ImmutableSet.copyOf(clocks);
	}

	public static ZonePrec of(final Collection<? extends ClockDecl> clocks) {
		return new ZonePrec(clocks);
	}

	public Set<ClockDecl> getClocks() {
		return clocks;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(clocks).toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ZonePrec) {
			final ZonePrec that = (ZonePrec) obj;
			return this.getClocks().equals(that.getClocks());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * clocks.hashCode();
	}
}
