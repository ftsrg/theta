package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph.atoms;

import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.core.type.LitExpr;

public class Write implements DatalogArgument {
    private final LitExpr<?> value;

    public Write(LitExpr<?> value) {
        this.value = value;
    }

    public LitExpr<?> getValue() {
        return value;
    }
}
