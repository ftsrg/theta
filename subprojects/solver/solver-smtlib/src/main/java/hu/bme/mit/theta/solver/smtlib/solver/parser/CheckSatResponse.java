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

import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Check_sat_responseContext;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException;

import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.PS_Sat;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.PS_Unknown;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.PS_Unsat;

public class CheckSatResponse extends SpecificResponse {

    private enum Status {
        SAT, UNSAT, UNKNOWN
    }

    private final Status status;

    private CheckSatResponse(Status status) {
        this.status = status;
    }

    public static CheckSatResponse fromContext(final Check_sat_responseContext ctx) {
        switch (ctx.value.getType()) {
            case PS_Sat:
                return new CheckSatResponse(Status.SAT);
            case PS_Unsat:
                return new CheckSatResponse(Status.UNSAT);
            case PS_Unknown:
                return new CheckSatResponse(Status.UNKNOWN);
            default:
                throw new SmtLibSolverException("Invalid interface");

        }
    }

    public boolean isSat() {
        return status == Status.SAT;
    }

    public boolean isUnsat() {
        return status == Status.UNSAT;
    }

    public boolean isUnknown() {
        return status == Status.UNKNOWN;
    }
}
