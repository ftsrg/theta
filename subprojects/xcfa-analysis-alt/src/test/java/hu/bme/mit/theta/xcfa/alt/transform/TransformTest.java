/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.transform;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.algorithm.XcfaChecker;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;

public class TransformTest {

    @Test
    public void simpleTransformationTest() throws IOException {
        final InputStream inputStream = getClass().getResourceAsStream("/functions-global-local.xcfa");
        XCFA xcfa = XcfaDslManager.createXcfa(inputStream);

        var checker = XcfaChecker.createChecker(xcfa, XcfaChecker.getSimpleExplicit().build());
        assert checker.check().isSafe();
    }
}
