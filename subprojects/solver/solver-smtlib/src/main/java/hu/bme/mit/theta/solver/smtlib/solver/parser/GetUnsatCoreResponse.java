package hu.bme.mit.theta.solver.smtlib.solver.parser;

import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Get_unsat_core_responseContext;
import org.antlr.v4.runtime.RuleContext;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;

public class GetUnsatCoreResponse extends SpecificResponse {
    private final Collection<String> labels;

    private GetUnsatCoreResponse(Collection<String> labels) {
        this.labels = labels;
    }

    public static GetUnsatCoreResponse fromContext(Get_unsat_core_responseContext ctx) {
        return new GetUnsatCoreResponse(
            ctx.symbol().stream().map(RuleContext::getText).collect(Collectors.toUnmodifiableSet())
        );
    }

    public static GetUnsatCoreResponse empty() {
        return new GetUnsatCoreResponse(Collections.emptyList());
    }

    public Collection<String> getLabels() {
        return labels;
    }
}
