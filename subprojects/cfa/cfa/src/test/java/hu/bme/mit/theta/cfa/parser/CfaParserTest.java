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
package hu.bme.mit.theta.cfa.parser;

import hu.bme.mit.theta.cfa.CFA;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class CfaParserTest {
    public String filepath;

    private Reader reader;
    private CfaParser parser;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"src/test/resources/counter5_true.lisp.cfa"},
                });
    }

    @BeforeEach
    public void before() throws FileNotFoundException {
        reader = new FileReader(filepath);
        parser = new CfaParser(reader);
    }

    @AfterEach
    public void after() throws IOException {
        reader.close();
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(String filepath) throws FileNotFoundException {
        initCfaParserTest(filepath);
        // Act
        final CFA cfa = parser.cfa();
        Assertions.assertEquals(1, cfa.getVars().size());
        Assertions.assertEquals(6, cfa.getLocs().size());
        Assertions.assertEquals(6, cfa.getEdges().size());
    }

    public void initCfaParserTest(String filepath) throws FileNotFoundException {
        this.filepath = filepath;
        this.before();
    }
}
