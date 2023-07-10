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
package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslLexer;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

public final class XstsDslManager {

    private XstsDslManager() {
    }

    public static XSTS createXsts(final String inputString) throws IOException {
        final InputStream stream = new ByteArrayInputStream(
                inputString.getBytes(StandardCharsets.UTF_8.name()));
        return createXsts(stream);
    }

    public static XSTS createXsts(final InputStream inputStream) throws IOException {
        final XstsDslLexer lexer = new XstsDslLexer(CharStreams.fromStream(inputStream));
        final CommonTokenStream tokenStream = new CommonTokenStream(lexer);
        final XstsDslParser parser = new XstsDslParser(tokenStream);
        final XstsDslParser.XstsContext model = parser.xsts();
        final XstsSpecification xstsSpecification = new XstsSpecification(model);

        return xstsSpecification.instantiate();
    }
}
