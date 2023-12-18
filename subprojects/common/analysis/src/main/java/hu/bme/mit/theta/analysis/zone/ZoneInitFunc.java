package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.InitFunc;

import java.util.Collection;
import java.util.Collections;

import static com.google.common.base.Preconditions.checkNotNull;

public class ZoneInitFunc implements InitFunc<ZoneState, ZonePrec> {

    private static final ZoneInitFunc INSTANCE = new ZoneInitFunc();

    private ZoneInitFunc() {
    }

    public static ZoneInitFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends ZoneState> getInitStates(ZonePrec prec) {
        checkNotNull(prec);
        return Collections.singleton(ZoneState.zero(prec.getVars()).transform().up().build());
    }
}
