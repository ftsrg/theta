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
package hu.bme.mit.theta.sts.aiger;

import hu.bme.mit.theta.sts.aiger.elements.AigerSystem;
import hu.bme.mit.theta.sts.aiger.utils.AigerCoi;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class AigerCoiTest {
    public String path;
    public int sizeOld;
    public int sizeNew;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"coi1.aag", 8, 3},
                    {"coi2.aag", 5, 3},
                    {"simple.aag", 6, 5},
                    {"simple2.aag", 6, 5},
                    {"simple3.aag", 7, 6},
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(String path, int sizeOld, int sizeNew) throws IOException {
        initAigerCoiTest(path, sizeOld, sizeNew);
        final AigerSystem system = AigerParser.parse("src/test/resources/" + path);
        Assertions.assertEquals(sizeOld, system.getNodes().size());
        AigerCoi.apply(system);
        Assertions.assertEquals(sizeNew, system.getNodes().size());
    }

    public void initAigerCoiTest(String path, int sizeOld, int sizeNew) {
        this.path = path;
        this.sizeOld = sizeOld;
        this.sizeNew = sizeNew;
    }
}
