/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Proof_responseContext;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.SortContext;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

public class GetProofResponse extends SpecificResponse {

    private final String proofTerm;
    private final Map<String, Tuple3<List<SortContext>, SortContext, String>>
            funDeclarations; // name -> [inSorts, outSort, declaration]

    private GetProofResponse(
            String proofNode,
            Map<String, Tuple3<List<SortContext>, SortContext, String>> funDeclarations) {
        this.proofTerm = proofNode;
        this.funDeclarations = funDeclarations;
    }

    public static GetProofResponse fromContext(final Proof_responseContext ctx) {
        return new GetProofResponse(
                extractString(ctx.proof_term().term()),
                ctx.proof_funs().stream()
                        .map(
                                it ->
                                        Tuple2.of(
                                                extractString(it.symbol()),
                                                Tuple3.of(it.in, it.out, extractString(it))))
                        .collect(Collectors.toMap(Tuple2::get1, Tuple2::get2)));
    }

    public static String extractString(final ParserRuleContext ctx) {
        return ctx.start
                .getInputStream()
                .getText(new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex()));
    }

    public String getProof() {
        return proofTerm;
    }

    public Map<String, Tuple3<List<SortContext>, SortContext, String>> getFunDeclarations() {
        return funDeclarations;
    }
}
