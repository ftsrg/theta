package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Set;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class ZonePrec implements Prec {

	private final Set<VarDecl<RatType>> clocks;

	private ZonePrec(final Collection<? extends VarDecl<RatType>> clocks) {
		checkNotNull(clocks);
		this.clocks = ImmutableSet.copyOf(clocks);
	}

	public static ZonePrec of(final Collection<? extends VarDecl<RatType>> clocks) {
		return new ZonePrec(clocks);
	}

	public Set<VarDecl<RatType>> getVars() {
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
			return this.getVars().equals(that.getVars());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * clocks.hashCode();
	}
}
