package hu.bme.mit.theta.xsts.analysis.timed;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.prod2.Prod2InitFunc;
import hu.bme.mit.theta.analysis.prod2.Prod2Ord;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.prod2.Prod2TransFunc;
import hu.bme.mit.theta.xsts.analysis.XstsAction;

import static com.google.common.base.Preconditions.checkNotNull;

public final class TimedXstsProd2Analysis<DState extends State, CState extends State, DPrec extends Prec, CPrec extends Prec>
        implements Analysis<Prod2State<DState, CState>, XstsAction, Prod2Prec<DPrec, CPrec>> {

    private final PartialOrd<Prod2State<DState, CState>> partialOrd;
    private final InitFunc<Prod2State<DState, CState>, Prod2Prec<DPrec, CPrec>> initFunc;
    private final TransFunc<Prod2State<DState, CState>, XstsAction, Prod2Prec<DPrec, CPrec>> transFunc;

    private TimedXstsProd2Analysis(final Analysis<DState, StmtAction, DPrec> dataAnalysis,
                                   final Analysis<CState, StmtAction, CPrec> clockAnalysis,
                                   final TimedXstsActionProjections actionProjections) {
        checkNotNull(dataAnalysis);
        checkNotNull(clockAnalysis);
        this.partialOrd = Prod2Ord.create(dataAnalysis.getPartialOrd(), clockAnalysis.getPartialOrd());
        this.initFunc = Prod2InitFunc.create(dataAnalysis.getInitFunc(), clockAnalysis.getInitFunc());

        final TransFunc<DState, XstsAction, DPrec> dataTransFunc = (state, action, prec)
                -> dataAnalysis.getTransFunc().getSuccStates(state, actionProjections.dataProjection(action), prec);
        final TransFunc<CState, XstsAction, CPrec> clockTransFunc = (state, action, prec)
                -> clockAnalysis.getTransFunc().getSuccStates(state, actionProjections.clockProjection(action), prec);
        this.transFunc = Prod2TransFunc.create(dataTransFunc, clockTransFunc);
    }

    public static <DState extends State, CState extends State, DPrec extends Prec, CPrec extends Prec> TimedXstsProd2Analysis<DState, CState, DPrec, CPrec> create(
            final Analysis<DState, StmtAction, DPrec> dataAnalysis,
            final Analysis<CState, StmtAction, CPrec> clockAnalysis,
            final TimedXstsActionProjections actionSplitter) {
        return new TimedXstsProd2Analysis<>(dataAnalysis, clockAnalysis, actionSplitter);
    }

    @Override
    public PartialOrd<Prod2State<DState, CState>> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<Prod2State<DState, CState>, Prod2Prec<DPrec, CPrec>> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<Prod2State<DState, CState>, XstsAction, Prod2Prec<DPrec, CPrec>> getTransFunc() {
        return transFunc;
    }
}
