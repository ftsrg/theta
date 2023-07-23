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

package hu.bme.mit.theta.cat.dsl;

import hu.bme.mit.theta.cat.dsl.gen.CatLexer;
import hu.bme.mit.theta.cat.dsl.gen.CatParser;
import hu.bme.mit.theta.graphsolver.patterns.constraints.GraphConstraint;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Collection;

public class CatDslManager {

    public static Collection<GraphConstraint> createMCM(final File file) throws IOException {
        final CatParser.McmContext context = setupCatAntlr(file);
        final hu.bme.mit.theta.cat.dsl.CatVisitor visitor = new hu.bme.mit.theta.cat.dsl.CatVisitor(file);
        context.accept(visitor);
        return visitor.getMcm();
    }

    static CatParser.McmContext setupCatAntlr(File file) throws IOException {
        FileInputStream inputStream = new FileInputStream(file);
        final CharStream input = CharStreams.fromStream(inputStream);

        final CatLexer lexer = new CatLexer(input);
        lexer.removeErrorListeners();
        lexer.addErrorListener(new FileNameAntlrErrorListener(file.getName()));
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        final CatParser parser = new CatParser(tokens);
        parser.removeErrorListeners();
        parser.addErrorListener(new FileNameAntlrErrorListener(file.getName()));
        inputStream.close();
        return parser.mcm();
    }

}
