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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2BaseVisitor;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Model_response_mathsatContext;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

import java.util.Collections;
import java.util.Map;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Get_model_responseContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Model_response_funContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Model_response_fun_recContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Model_response_funs_recContext;

public class GetModelResponse extends SpecificResponse {

    private final SmtLibModel model;

    private GetModelResponse(final Map<String, String> values) {
        model = new SmtLibModel(values);
    }

    public static GetModelResponse fromContext(final Get_model_responseContext ctx) {
        return new GetModelResponse(ctx.model_response().stream()
                .map(member -> member.accept(new SMTLIBv2BaseVisitor<Tuple2<String, String>>() {
                    @Override
                    public Tuple2<String, String> visitModel_response_fun(
                            Model_response_funContext ctx) {
                        return Tuple2.of(extractString(ctx.function_def().symbol()),
                                extractString(ctx.function_def()));
                    }

                    @Override
                    public Tuple2<String, String> visitModel_response_mathsat(
                            Model_response_mathsatContext ctx) {
                        final var functionDef = String.format(
                                "%s () (_ theta_type unknown) %s",
                                extractString(ctx.symbol()),
                                extractString(ctx.term())
                        );
                        return Tuple2.of(extractString(ctx.symbol()), functionDef);
                    }

                    @Override
                    public Tuple2<String, String> visitModel_response_fun_rec(
                            Model_response_fun_recContext ctx) {
                        throw new UnsupportedOperationException();
                    }

                    @Override
                    public Tuple2<String, String> visitModel_response_funs_rec(
                            Model_response_funs_recContext ctx) {
                        throw new UnsupportedOperationException();
                    }
                })).collect(Collectors.toUnmodifiableMap(Tuple2::get1, Tuple2::get2)));
    }

    public static GetModelResponse empty() {
        return new GetModelResponse(Collections.emptyMap());
    }

    public SmtLibModel getModel() {
        return model;
    }

    public static String extractString(final ParserRuleContext ctx) {
        return ctx.start.getInputStream()
                .getText(new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex()));
    }
}
