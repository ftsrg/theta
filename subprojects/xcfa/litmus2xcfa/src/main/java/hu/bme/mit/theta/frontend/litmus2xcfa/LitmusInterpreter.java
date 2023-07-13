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

package hu.bme.mit.theta.frontend.litmus2xcfa;

import hu.bme.mit.theta.frontend.litmus2xcfa.dsl.LitmusAArch64;
import hu.bme.mit.theta.litmus2xcfa.dsl.gen.LitmusAArch64Lexer;
import hu.bme.mit.theta.litmus2xcfa.dsl.gen.LitmusAArch64Parser;
import hu.bme.mit.theta.xcfa.model.XCFA;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Lexer;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

public class LitmusInterpreter {

    public static XCFA getXcfa(final File from) throws IOException {
        try (FileInputStream fis = new FileInputStream(from)) {
            return getXcfa(fis);
        }
    }

    public static XCFA getXcfa(final InputStream from) throws IOException {
        final CharStream input = CharStreams.fromStream(from);

        final Lexer lexer = new LitmusAArch64Lexer(input);
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        final LitmusAArch64 visitor = new LitmusAArch64();

        return new LitmusAArch64Parser(tokens).main().accept(visitor);
    }
}
