package hu.bme.mit.theta.xcfa.analysis.common.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.StaticAutoExpl;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.util.Set;

public class XcfaGlobalStaticAutoExpl implements XcfaAutoExpl {
    @Override
    public AutoExpl create(XCFA xcfa) {
        return new StaticAutoExpl(Set.copyOf(xcfa.getGlobalVars()));
    }
}
