/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.solver.smtlib.solver.parser;

import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2BaseVisitor;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.General_response_errorContext;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.General_response_successContext;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.General_response_unsupportedContext;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.ResponseContext;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Specific_success_responseContext;

import static com.google.common.base.Preconditions.checkState;

public class GeneralResponse {

    private final boolean successful;
    private final String reason;
    private final SpecificResponse specificResponse;

    private GeneralResponse(boolean successful, String reason, SpecificResponse specificResponse) {
        this.successful = successful;
        this.reason = reason;
        this.specificResponse = specificResponse;
    }

    public static GeneralResponse fromContext(final ResponseContext ctx) {
        return ctx.accept(new SMTLIBv2BaseVisitor<>() {
            @Override
            public GeneralResponse visitGeneral_response_success(
                    General_response_successContext ctx) {
                return new GeneralResponse(true, null, null);
            }

            @Override
            public GeneralResponse visitGeneral_response_unsupported(
                    General_response_unsupportedContext ctx) {
                return new GeneralResponse(false, "Unsupported", null);
            }

            @Override
            public GeneralResponse visitSpecific_success_response(
                    Specific_success_responseContext ctx) {
                return new GeneralResponse(true, null, SpecificResponse.fromContext(ctx));
            }

            @Override
            public GeneralResponse visitGeneral_response_error(General_response_errorContext ctx) {
                return new GeneralResponse(false, ctx.reason.getText(), null);
            }
        });
    }

    public boolean isSuccessful() {
        return successful && specificResponse == null;
    }

    public boolean isError() {
        return !successful;
    }

    public String getReason() {
        checkState(isError());
        return reason;
    }

    public boolean isSpecific() {
        return successful && specificResponse != null;
    }

    public SpecificResponse asSpecific() {
        checkState(isSpecific());
        return specificResponse;
    }
}
