package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.DiffBounds;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.XtaSystem;

import java.util.Collection;
import java.util.Map;

public class XtaInitClockPredPrec {

    private static boolean shouldApplyDelay = false;

    public static void setShouldApplyDelay(boolean _shouldApplyDelay){
        shouldApplyDelay = _shouldApplyDelay;
    }

    private static ClockPredPrec addZeroToClockPredMap(ClockPredPrec prec, Collection<VarDecl<RatType>> clocks){
        for (VarDecl<RatType> clock : clocks){
            prec.add(clock, DiffBounds.Leq(0));
        }
        return prec;
    }
    public static Prod2Prec<PredPrec, ClockPredPrec> createEmptyProd2PredClockPred(XtaSystem xta){
        PredPrec predPrec = PredPrec.of();
        ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
        if(!shouldApplyDelay){
            clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());
        }
        return Prod2Prec.of(predPrec, clockPredPrec);
    }

    public static LocalXtaPrec<Prod2Prec<PredPrec, ClockPredPrec>> collectLocalProd2PredClockPred(XtaSystem xta) {
        Map<XtaProcess.Loc, Prod2Prec<PredPrec, ClockPredPrec>> mapping = Containers.createMap();
        for(XtaProcess proc: xta.getProcesses()){
            for (XtaProcess.Loc l : proc.getActiveClockMap().keySet()){

                ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
                if(!shouldApplyDelay && xta.getInitLocs().contains(l)) clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());
                mapping.put(l, Prod2Prec.of(PredPrec.of(), clockPredPrec));
            }
        }
        ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
        if(!shouldApplyDelay) clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());
        return LocalXtaPrec.create(mapping, Prod2Prec.of(PredPrec.of(), clockPredPrec));
    }


    public static LocalXtaPrec<Prod2Prec<PredPrec, ClockPredPrec>> collectLocalProd2PredClockPred_Active(XtaSystem xta) {
        Map<XtaProcess.Loc, Prod2Prec<PredPrec, ClockPredPrec>> mapping = Containers.createMap();
        for(XtaProcess proc: xta.getProcesses()){
            for (XtaProcess.Loc l : proc.getActiveClockMap().keySet()){
                ClockPredPrec clockPredPrec = ClockPredPrec.of(proc.getActiveClockMap().get(l));
                if(!shouldApplyDelay && xta.getInitLocs().contains(l)) clockPredPrec = addZeroToClockPredMap(clockPredPrec, proc.getActiveClockMap().get(l));

                mapping.put(l, Prod2Prec.of(PredPrec.of(), clockPredPrec));
            }
        }
        ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
        if(!shouldApplyDelay) clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());
        return LocalXtaPrec.create(mapping, Prod2Prec.of(PredPrec.of(), clockPredPrec));
    }

    public static GlobalXtaPrec<Prod2Prec<PredPrec,  ClockPredPrec>> collectGlobalProd2PredClockPred(XtaSystem xta) {
        PredPrec predPrec = PredPrec.of();
        ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
        if(!shouldApplyDelay){
            clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());
        }
        return GlobalXtaPrec.create(Prod2Prec.of(predPrec, clockPredPrec));
    }

    public static Prod2Prec<ExplPrec,  ClockPredPrec> createEmptyProd2ExplClockPred(XtaSystem xta) {
        ExplPrec explPrec = ExplPrec.empty();
        ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
        if(!shouldApplyDelay){
            clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());
        }
        return Prod2Prec.of(explPrec, clockPredPrec);
    }

    public static XtaPrec<Prod2Prec<ExplPrec, ClockPredPrec>> collectLocalProd2ExplClockPred(XtaSystem xta) {
        Map<XtaProcess.Loc, Prod2Prec<ExplPrec, ClockPredPrec>> mapping = Containers.createMap();
        for(XtaProcess proc: xta.getProcesses()){
            for (XtaProcess.Loc l : proc.getActiveClockMap().keySet()){
                ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
                if(!shouldApplyDelay && xta.getInitLocs().contains(l)) clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());

                mapping.put(l, Prod2Prec.of(ExplPrec.empty(),clockPredPrec));
            }
        }
        ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
        if(!shouldApplyDelay) clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());
        return LocalXtaPrec.create(mapping, Prod2Prec.of(ExplPrec.empty(), clockPredPrec));
    }
    public static XtaPrec<Prod2Prec<ExplPrec, ClockPredPrec>> collectLocalProd2ExplClockPred_Active(XtaSystem xta) {
        Map<XtaProcess.Loc, Prod2Prec<ExplPrec, ClockPredPrec>> mapping = Containers.createMap();
        for(XtaProcess proc: xta.getProcesses()){
            for (XtaProcess.Loc l : proc.getActiveClockMap().keySet()){
                ClockPredPrec clockPredPrec = ClockPredPrec.of(proc.getActiveClockMap().get(l));
                if(!shouldApplyDelay && xta.getInitLocs().contains(l)) clockPredPrec = addZeroToClockPredMap(clockPredPrec, proc.getActiveClockMap().get(l));

                mapping.put(l, Prod2Prec.of(ExplPrec.empty(),clockPredPrec));
            }
        }
        ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
        if(!shouldApplyDelay) clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());
        return LocalXtaPrec.create(mapping, Prod2Prec.of(ExplPrec.empty(), clockPredPrec));
    }

    public static XtaPrec<Prod2Prec<ExplPrec,  ClockPredPrec>> collectGlobalProd2ExplClockPred(XtaSystem xta) {
        ExplPrec explPrec = ExplPrec.empty();
        ClockPredPrec clockPredPrec = ClockPredPrec.of(xta.getClockVars());
        if(!shouldApplyDelay){
            clockPredPrec = addZeroToClockPredMap(clockPredPrec, xta.getClockVars());
        }
        return GlobalXtaPrec.create(Prod2Prec.of(explPrec, clockPredPrec));
    }
}
