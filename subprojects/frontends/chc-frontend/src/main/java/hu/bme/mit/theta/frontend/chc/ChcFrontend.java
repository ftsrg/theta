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
package hu.bme.mit.theta.frontend.chc;

import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCLexer;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.xcfa.model.XcfaBuilder;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;

public class ChcFrontend {

    public enum ChcTransformation {
        PORTFOLIO,
        FORWARD,
        BACKWARD
    }

    private final ChcTransformation chcTransformation;

    public ChcFrontend(ChcTransformation transformation) {
        chcTransformation = transformation;
    }

    public XcfaBuilder buildXcfa(CharStream charStream) {
        ChcUtils.init(charStream);
        CHCParser parser = new CHCParser(new CommonTokenStream(new CHCLexer(charStream)));
        ChcXcfaBuilder chcXcfaBuilder = switch (chcTransformation) {
            case FORWARD -> new ChcForwardXcfaBuilder();
            case BACKWARD -> new ChcBackwardXcfaBuilder();
            default ->
                    throw new RuntimeException("Should not be here; adapt PORTFOLIO to FW/BW beforehand.");
        };
        return chcXcfaBuilder.buildXcfa(parser);
    }
}

