package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.lazy.*;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.xta.analysis.*;

import static com.google.common.base.Preconditions.checkNotNull;

public class CombinedLazyCegarXtaCheckerConfig<DConcr extends State, CConcr extends State, DAbstr extends ExprState, CAbstr extends ExprState, DPrec extends Prec, CPrec extends Prec> {
    private final CegarChecker<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, Prod2Prec<DPrec, CPrec>> cegarChecker;
    private final Prod2Prec<DPrec, CPrec> prec;

    public CombinedLazyCegarXtaCheckerConfig(
        final CegarChecker<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, Prod2Prec<DPrec, CPrec>> cegarChecker,
        final Prod2Prec<DPrec, CPrec> prec
    ) {
        this.cegarChecker = cegarChecker;
        this.prec = prec;
    }

    public SafetyResult<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction> check() {
        return cegarChecker.check(prec);
    }
}
