package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.DBM;
import hu.bme.mit.theta.analysis.zone.ZoneState;

import java.util.Collection;
import java.util.Collections;

import static com.google.common.base.Preconditions.checkNotNull;

public class ClockPredInitFunc implements InitFunc<ZoneState, ClockPredPrec> {

    final DBM initdbm;
    private ClockPredInitFunc(DBM initdbm){
        this.initdbm = initdbm;
    }

    public static ClockPredInitFunc create(DBM initdbm){
        return new ClockPredInitFunc(initdbm);
    }
    @Override
    public Collection<ZoneState> getInitStates(ClockPredPrec prec)
    {
        checkNotNull(prec);
        Collection<ZoneState> initstates = Collections.singleton(ZoneState.of(initdbm));
        initstates.stream().forEach(zoneState -> zoneState.clockPredicate(prec));
        return initstates;
    }
}
