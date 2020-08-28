package hu.bme.mit.theta.solver.smtlib.parser;

import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2BaseVisitor;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Specific_success_responseContext;

public interface SpecificResponse {
    static SpecificResponse fromContext(final Specific_success_responseContext ctx) {
        return ctx.accept(new SMTLIBv2BaseVisitor<>() {
            @Override
            public SpecificResponse visitCheck_sat_response(SMTLIBv2Parser.Check_sat_responseContext ctx) {
                return CheckSatResponse.fromContext(ctx);
            }
        });
    }
}
