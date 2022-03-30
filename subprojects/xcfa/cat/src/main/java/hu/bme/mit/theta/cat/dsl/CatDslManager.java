/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.cat.dsl;

import hu.bme.mit.theta.cat.dsl.gen.CatLexer;
import hu.bme.mit.theta.cat.dsl.gen.CatParser;
import hu.bme.mit.theta.cat.mcm.MCM;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

public class CatDslManager {

    public static MCM createMCM(final InputStream inputStream) throws IOException {
        final CharStream input = CharStreams.fromStream(inputStream);

        final CatLexer lexer = new CatLexer(input);
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        final CatParser parser = new CatParser(tokens);

        final CatParser.McmContext context = parser.mcm();

        final hu.bme.mit.theta.cat.dsl.CatVisitor visitor = new hu.bme.mit.theta.cat.dsl.CatVisitor();
        context.accept(visitor);

        return visitor.getMcm();
    }

    public static MCM createMCM(final String s) throws IOException {
        return createMCM(new ByteArrayInputStream(s.getBytes(StandardCharsets.UTF_8)));
    }

}
