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
package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker.IterationStrategy;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

@Disabled // causes CI runners to give up
public class XstsSatMddCheckerTest {
    public String filePath;
    public String propPath;
    public boolean safe;

    public static java.util.Collection<Object[]> data() {
        return XstsMddCheckerTest.data();
    }

    @MethodSource("data")
    @ParameterizedTest(name = "{index}: {0}, {1}, {2}")
    public void test(String filePath, String propPath, boolean safe) throws Exception {
        initXstsSatMddCheckerTest(filePath, propPath, safe);
        XstsMddCheckerTest.runTestWithIterationStrategy(
                filePath, propPath, safe, IterationStrategy.SAT);
    }

    public void initXstsSatMddCheckerTest(String filePath, String propPath, boolean safe) {
        this.filePath = filePath;
        this.propPath = propPath;
        this.safe = safe;
    }
}
