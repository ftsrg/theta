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
package hu.bme.mit.theta.cfa.dsl;

import hu.bme.mit.theta.cfa.CFA;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class CfaDslManagerTest {
    public String filepath;
    public int varCount;
    public int locCount;
    public int edgeCount;
    public int stmtCount;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"/locking.cfa", 3, 9, 10, 10},
                    {"/counter5_true.cfa", 1, 6, 6, 6},
                    {"/bv.cfa", 1, 6, 6, 6},
                    {"/bv2.cfa", 1, 6, 6, 6},
                    {"/bv3.cfa", 1, 6, 6, 6},
                    {"/bv4.cfa", 2, 7, 8, 8},
                    {"/fp1.cfa", 4, 7, 6, 6},
                    {"/fp2.cfa", 4, 7, 6, 6}
                });
    }

    @MethodSource("data")
    @ParameterizedTest()
    public void test(String filepath, int varCount, int locCount, int edgeCount, int stmtCount) throws IOException {
        initCfaDslManagerTest(filepath, varCount, locCount, edgeCount, stmtCount);
        final InputStream inputStream = getClass().getResourceAsStream(filepath);
        final CFA cfa = CfaDslManager.createCfa(inputStream);
        Assertions.assertEquals(varCount, cfa.getVars().size());
        Assertions.assertEquals(locCount, cfa.getLocs().size());
        Assertions.assertEquals(edgeCount, cfa.getEdges().size());
        Assertions.assertEquals(stmtCount, cfa.getEdges().stream().map(e -> e.getStmt()).count());
    }

    public void initCfaDslManagerTest(String filepath, int varCount, int locCount, int edgeCount, int stmtCount) {
        this.filepath = filepath;
        this.varCount = varCount;
        this.locCount = locCount;
        this.edgeCount = edgeCount;
        this.stmtCount = stmtCount;
    }
}
