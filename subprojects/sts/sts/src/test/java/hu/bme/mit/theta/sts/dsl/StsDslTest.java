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
package hu.bme.mit.theta.sts.dsl;

import hu.bme.mit.theta.sts.STS;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class StsDslTest {
    public String filepath;
    public String propertyName;
    public int varCount;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"/readerswriters.system", "safe", 3},
                    {"/simple1.system", "safe", 2}
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(String filepath, String propertyName, int varCount) throws FileNotFoundException, IOException {
        initStsDslTest(filepath, propertyName, varCount);
        final InputStream inputStream = StsDslTest.class.getResourceAsStream(filepath);
        final StsSpec spec = StsDslManager.createStsSpec(inputStream);
        final STS sts = spec.createProp(propertyName);
        Assertions.assertEquals(varCount, sts.getVars().size());
    }

    public void initStsDslTest(String filepath, String propertyName, int varCount) {
        this.filepath = filepath;
        this.propertyName = propertyName;
        this.varCount = varCount;
    }
}
