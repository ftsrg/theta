package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.xta.XtaSystem;

public class XtaEmptyInitPrec implements XtaInitPrec {
    @Override
    public Prod2Prec<PredPrec, ZonePrec> createProd2PredZone(XtaSystem xta) {
        return Prod2Prec.of(PredPrec.of(), ZonePrec.of(xta.getClockVars()));
    }
}
