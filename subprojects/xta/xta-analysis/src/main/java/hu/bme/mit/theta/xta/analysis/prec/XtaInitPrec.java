package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.xta.XtaSystem;

public interface XtaInitPrec {
    Prod2Prec<PredPrec, ZonePrec> createProd2PredZone(XtaSystem xta);
}
