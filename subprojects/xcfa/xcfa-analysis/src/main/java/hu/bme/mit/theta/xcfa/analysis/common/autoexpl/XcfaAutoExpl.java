package hu.bme.mit.theta.xcfa.analysis.common.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.xcfa.model.XCFA;

public interface XcfaAutoExpl {

    AutoExpl create(final XCFA xcfa);

}
