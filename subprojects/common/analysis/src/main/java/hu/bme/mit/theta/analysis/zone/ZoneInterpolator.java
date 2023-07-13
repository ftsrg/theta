package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Interpolator;

import java.util.Collection;

public final class ZoneInterpolator implements Interpolator<ZoneState, ZoneState> {

    private static final ZoneInterpolator INSTANCE = new ZoneInterpolator();

    private ZoneInterpolator() {
    }

    public static ZoneInterpolator getInstance() {
        return INSTANCE;
    }

    @Override
    public ZoneState toItpDom(final ZoneState zone) {
        return zone;
    }

    @Override
    public ZoneState interpolate(final ZoneState zone1, final ZoneState zone2) {
        return ZoneState.interpolant(zone1, zone2);
    }

    @Override
    public Collection<ZoneState> complement(final ZoneState zone) {
        return zone.complement();
    }

    @Override
    public boolean refutes(final ZoneState zone1, final ZoneState zone2) {
        return !zone1.isConsistentWith(zone2);
    }
}
