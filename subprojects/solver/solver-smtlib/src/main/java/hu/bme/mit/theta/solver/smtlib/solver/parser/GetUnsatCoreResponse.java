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
