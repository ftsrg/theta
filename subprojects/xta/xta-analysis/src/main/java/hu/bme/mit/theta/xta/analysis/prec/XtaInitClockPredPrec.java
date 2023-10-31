package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.XtaSystem;

import java.time.Clock;
import java.util.Collections;
import java.util.Map;

public class XtaInitClockPredPrec {

    public static Prod2Prec<PredPrec, ClockPredPrec> createEmptyProd2PredZone(XtaSystem xta){
        return Prod2Prec.of(PredPrec.of(), ClockPredPrec.of(xta.getClockVars()));
    }

    public static Prod2Prec<PredPrec, ClockPredPrec> createEmptyZoneProd2PredZone(XtaSystem xta) {
        return Prod2Prec.of(PredPrec.of(), ClockPredPrec.of(Collections.emptySet()));
    }
    public static LocalXtaPrec<Prod2Prec<PredPrec, ClockPredPrec>> collectLocalProd2PredZone(XtaSystem xta) {
        Map<XtaProcess.Loc, Prod2Prec<PredPrec, ClockPredPrec>> mapping = Containers.createMap();
        for(XtaProcess proc: xta.getProcesses()){
            for (XtaProcess.Loc l : proc.getActiveClockMap().keySet()){
                mapping.put(l, Prod2Prec.of(PredPrec.of(), ClockPredPrec.of(proc.getActiveClockMap().get(l))));
            }
        }
        return LocalXtaPrec.create(mapping, Prod2Prec.of(PredPrec.of(), ClockPredPrec.of(xta.getClockVars())));
    }

    public static GlobalXtaPrec<Prod2Prec<PredPrec,  ClockPredPrec>> collectGlobalProd2PredZone(XtaSystem xta) {
        return GlobalXtaPrec.create(Prod2Prec.of(PredPrec.of(), ClockPredPrec.of(xta.getClockVars())));
    }

    public static Prod2Prec<ExplPrec,  ClockPredPrec> createEmptyProd2ExplZone(XtaSystem xta) {
        return Prod2Prec.of(ExplPrec.empty(), ClockPredPrec.of(xta.getClockVars()));
    }

    public static XtaPrec<Prod2Prec<ExplPrec, ClockPredPrec>> collectLocalProd2ExplZone(XtaSystem xta) {
        Map<XtaProcess.Loc, Prod2Prec<ExplPrec, ClockPredPrec>> mapping = Containers.createMap();
        for(XtaProcess proc: xta.getProcesses()){
            for (XtaProcess.Loc l : proc.getActiveClockMap().keySet()){
                mapping.put(l, Prod2Prec.of(ExplPrec.empty(), ClockPredPrec.of(proc.getActiveClockMap().get(l))));
            }
        }
        return LocalXtaPrec.create(mapping, Prod2Prec.of(ExplPrec.empty(), ClockPredPrec.of(xta.getClockVars())));
    }

    public static XtaPrec<Prod2Prec<ExplPrec,  ClockPredPrec>> collectGlobalProd2ExplZone(XtaSystem xta) {
        return GlobalXtaPrec.create(Prod2Prec.of(ExplPrec.empty(), ClockPredPrec.of(xta.getClockVars())));
    }
}
