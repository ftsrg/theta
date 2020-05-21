package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.stmt.NonDetStmt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

public class XstsInitFunc<S extends ExprState, P extends Prec> implements InitFunc<XstsState<S>,P> {

    private final InitFunc<S, ? super P> initFunc;

    private XstsInitFunc(final InitFunc<S, ? super P> initFunc){
        this.initFunc=initFunc;
    }

    public static <S extends ExprState, P extends Prec> XstsInitFunc<S,P> create(final InitFunc<S,? super P> initFunc){
        return new XstsInitFunc<>(initFunc);
    }

    @Override
    public Collection<? extends XstsState<S>> getInitStates(final P prec) {
        final Collection<XstsState<S>> initStates = new ArrayList<>();
        for(final S subInitState: initFunc.getInitStates(prec)) {
            initStates.add(XstsState.of(subInitState, false));
        }
        return initStates;
    }
}
