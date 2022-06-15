package hu.bme.mit.theta.xsts.analysis.config;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.tracegen.TraceGenChecker;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;

import java.util.List;

public class XstsTracegenConfig<S extends ExprState, A extends StmtAction, P extends Prec> {

    private final TraceGenChecker<S, A, P> checker;
    private final P initPrec;

    private XstsTracegenConfig(final TraceGenChecker<S, A, P> checker, final P initPrec) {
        this.checker = checker;
        this.initPrec = initPrec;
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> XstsTracegenConfig<S, A, P> create(
            final TraceGenChecker<S, A, P> checker, final P initPrec) {
        return new XstsTracegenConfig<S,A,P>(checker, initPrec);
    }

    public SafetyResult<S, A> check() {
        return checker.check(initPrec);
    }

    public List<Trace<S, A>> getTraces() {
        return checker.getTraces();
    }
}
