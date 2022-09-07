package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.xta.analysis.XtaAction;

public class CombinedLazyCegarXtaAnalysis<S extends State, P extends Prec> implements Analysis<S, XtaAction, P> {

    private final Analysis<S, ? super StmtAction, P> analysis;

    private final TransFunc<S, XtaAction, P> transFunc;

    private CombinedLazyCegarXtaAnalysis(final Analysis<S, ? super StmtAction, P> analysis) {
        this.analysis = analysis;
        this.transFunc = CombinedLazyCegarXtaTransFunc.create(analysis.getTransFunc());
    }

    public static <S extends State, P extends Prec> CombinedLazyCegarXtaAnalysis<S, P> create(final Analysis<S, ? super StmtAction, P> analysis) {
        return new CombinedLazyCegarXtaAnalysis<>(analysis);
    }

    @Override
    public PartialOrd<S> getPartialOrd() {
        return analysis.getPartialOrd();
    }

    @Override
    public InitFunc<S, P> getInitFunc() {
        return analysis.getInitFunc();
    }

    @Override
    public TransFunc<S, XtaAction, P> getTransFunc() {
        return transFunc;
    }
}
