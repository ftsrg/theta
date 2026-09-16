/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.frontend.svlib;

import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager;
import org.antlr.v4.runtime.*;

import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibLexer;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

import static java.util.Objects.requireNonNull;

public class SvLibFrontend{

    private final ProcedurePassManager procedurePassManager;

    public SvLibFrontend() {
        this(new ProcedurePassManager());
    }

    public SvLibFrontend(ProcedurePassManager procedurePassManager) {
        this.procedurePassManager = requireNonNull(procedurePassManager);
    }

    public XCFA buildXcfa(File input) {
        try {
            return buildXcfa(Files.readString(input.toPath()));
        } catch (IOException e) {
            throw new IllegalStateException("Failed to read SV-LIB input from " + input, e);
        }
    }

    public XCFA buildXcfa(String source) {
        SvLibParser parser = createParser(source);
        SvLibParser.ScriptContext script = parser.script();
        return new SvLibXcfaBuilder(procedurePassManager).buildXcfa(script);
    }

    private SvLibParser createParser(String source) {
        CharStream charStream = CharStreams.fromString(source);
        SvLibUtils.init(charStream);
        SvLibLexer lexer = new SvLibLexer(charStream);
        SvLibParser parser = new SvLibParser(new CommonTokenStream(lexer));
        parser.setErrorHandler(new BailErrorStrategy());
        return parser;
    }

}
