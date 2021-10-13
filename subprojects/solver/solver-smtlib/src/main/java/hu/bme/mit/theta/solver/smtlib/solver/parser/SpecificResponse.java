package hu.bme.mit.theta.solver.smtlib.solver.parser;

import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2BaseVisitor;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Specific_success_responseContext;

import static com.google.common.base.Preconditions.checkState;

public abstract class SpecificResponse {
    static SpecificResponse fromContext(final Specific_success_responseContext ctx) {
        return ctx.accept(new SMTLIBv2BaseVisitor<>() {
            @Override
            public SpecificResponse visitCheck_sat_response(SMTLIBv2Parser.Check_sat_responseContext ctx) {
                return CheckSatResponse.fromContext(ctx);
            }

            @Override
            public SpecificResponse visitGet_unsat_core_response(SMTLIBv2Parser.Get_unsat_core_responseContext ctx) {
                return GetUnsatCoreResponse.fromContext(ctx);
            }

            @Override
            public SpecificResponse visitGet_model_response(SMTLIBv2Parser.Get_model_responseContext ctx) {
                return GetModelResponse.fromContext(ctx);
            }
        });
    }

    public boolean isCheckSatResponse() {
        return this instanceof CheckSatResponse;
    }

    public boolean isGetUnsatCoreResponse() {
        return
            this instanceof GetUnsatCoreResponse ||
            this instanceof GetModelResponse && ((GetModelResponse) this).getModel().size() == 0;
    }

    public boolean isGetModelResponse() {
        return
            this instanceof GetModelResponse ||
            this instanceof GetUnsatCoreResponse && ((GetUnsatCoreResponse) this).getLabels().size() == 0;
    }

    public CheckSatResponse asCheckSatResponse() {
        checkState(isCheckSatResponse());
        return (CheckSatResponse) this;
    }

    public GetUnsatCoreResponse asGetUnsatCoreResponse() {
        checkState(isGetUnsatCoreResponse());
        if(this instanceof GetUnsatCoreResponse) {
            return (GetUnsatCoreResponse) this;
        }
        else if(this instanceof GetModelResponse) {
            return GetUnsatCoreResponse.empty();
        }
        else {
            throw new AssertionError();
        }
    }

    public GetModelResponse asGetModelResponse() {
        checkState(isGetModelResponse());
        if(this instanceof GetModelResponse) {
            return (GetModelResponse) this;
        }
        else if(this instanceof GetUnsatCoreResponse) {
            return GetModelResponse.empty();
        }
        else {
            throw new AssertionError();
        }
    }
}
