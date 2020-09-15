package hu.bme.mit.theta.solver.smtlib.z3;

import hu.bme.mit.theta.solver.smtlib.SmtLibItpMarker;

public class Z3SmtLibItpMarker extends SmtLibItpMarker {
    private static final String markerPattern = "_z3_marker_%d";
    private static long markerCount = 0;

    static void resetMarkerCount() {
        markerCount = 0;
    }

    private final String markerName;

    public Z3SmtLibItpMarker() {
        super();
        markerName = String.format(markerPattern, markerCount++);
    }

    public String getMarkerName() {
        return markerName;
    }
}
