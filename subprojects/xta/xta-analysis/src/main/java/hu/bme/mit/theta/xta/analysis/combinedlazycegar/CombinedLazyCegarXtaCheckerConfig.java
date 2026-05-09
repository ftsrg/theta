package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.Proof;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;

public class CombinedLazyCegarXtaCheckerConfig<DPrec extends Prec, CPrec extends Prec, Pr extends Proof, C extends Cex> {

    private final CegarChecker<Prod2Prec<DPrec, CPrec>, Pr, C> cegarChecker;
    private final Prod2Prec<DPrec, CPrec> prec;

    public CombinedLazyCegarXtaCheckerConfig(
        final CegarChecker<Prod2Prec<DPrec, CPrec>, Pr, C> cegarChecker,
        final Prod2Prec<DPrec, CPrec> prec
    ) {
        this.cegarChecker = cegarChecker;
        this.prec = prec;
    }

    public SafetyResult<Pr, C> check() {
        return cegarChecker.check(prec);
    }
}
