package hu.bme.mit.inf.theta.solver;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkArgument;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.Lists;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;

public interface ItpSolver extends Solver {

	public ItpPattern createPattern(final ItpMarker marker);
	
	public default ItpPattern createBinPattern(final ItpMarker markerA, final ItpMarker markerB) {
		if (markerA == null || markerB == null) {
			throw new NullPointerException();
		}
		
		return createSeqPattern(Arrays.asList(markerA, markerB));
	}
	
	public default ItpPattern createSeqPattern(final List<? extends ItpMarker> markers) {
		checkNotNull(markers);
		checkArgument(!markers.isEmpty());
		
		ItpPattern result = null;
		ItpPattern current = null;
		
		for (ItpMarker marker : Lists.reverse(markers)) {
			if (result == null) {
				current = createPattern(marker);
				result = current;
			} else {
				current = current.createChild(marker);
			}
		}
		return result;
	}
	
	public ItpMarker createMarker();

	public void add(final ItpMarker marker, final Expr<? extends BoolType> assertion);
	public default void add(final ItpMarker marker, final Collection<? extends Expr<? extends BoolType>> assertions) {
		checkNotNull(marker);
		checkNotNull(assertions);
		for (Expr<? extends BoolType> assertion : assertions) {
			add(marker, assertion);
		}
	}

	public Interpolant getInterpolant(final ItpPattern pattern);

	public Collection<ItpMarker> getMarkers();

}
