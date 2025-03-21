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
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class PrecisionResponse extends SpecificResponse {
    private final Collection<String> terms;
    private final Map<String, Tuple3<List<SMTLIBv2Parser.SortContext>, SMTLIBv2Parser.SortContext, String>>
            funDeclarations; // name -> [inSorts, outSort, declaration]

    private PrecisionResponse(
            Collection<String> terms,
            Map<String, Tuple3<List<SMTLIBv2Parser.SortContext>, SMTLIBv2Parser.SortContext, String>> funDeclarations) {
        this.terms = terms;
        this.funDeclarations = funDeclarations;
    }

    public static PrecisionResponse fromContext(final SMTLIBv2Parser.Precision_responseContext ctx) {
        return new PrecisionResponse(
                ctx.term().stream()
                        .map(PrecisionResponse::extractString)
                        .collect(Collectors.toList()),
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

    public Collection<String> getTerms() {
        return terms;
    }

    public Map<String, Tuple3<List<SMTLIBv2Parser.SortContext>, SMTLIBv2Parser.SortContext, String>> getFunDeclarations() {
        return funDeclarations;
    }
}
