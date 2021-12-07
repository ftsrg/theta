package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.PartialOrd;

public final class ZoneLattice implements Lattice<ZoneState> {

    private final PartialOrd<ZoneState> partialOrd;

    private static final ZoneLattice INSTANCE = new ZoneLattice();

    private ZoneLattice() {
        partialOrd = ZoneOrd.getInstance();
    }

    public static ZoneLattice getInstance() {
        return INSTANCE;
    }

    @Override
    public ZoneState top() {
        return ZoneState.top();
    }

    @Override
    public ZoneState bottom() {
        return ZoneState.bottom();
    }

    @Override
    public ZoneState meet(final ZoneState state1, final ZoneState state2) {
        return ZoneState.intersection(state1, state2);
    }

    @Override
    public ZoneState join(final ZoneState state1, final ZoneState state2) {
        return ZoneState.enclosure(state1, state2);
    }

    @Override
    public boolean isLeq(final ZoneState state1, final ZoneState state2) {
        return partialOrd.isLeq(state1, state2);
    }
}
