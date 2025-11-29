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
package hu.bme.mit.theta.xta.dsl;

import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.XtaVisualizer;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class XtaDslManagerTest {

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"/critical-4-25-50.xta"},
                    {"/csma-4.xta"},
                    {"/fddi-4.xta"},
                    {"/fischer-4-32-64.xta"},
                    {"/lynch-4-16.xta"}
                });
    }
    public String filepath;

    @MethodSource("data")
    @ParameterizedTest(name = "{0}")
    public void test(String filepath) throws FileNotFoundException, IOException {
        initXtaDslManagerTest(filepath);
        final InputStream inputStream = getClass().getResourceAsStream(filepath);
        final XtaSystem system = XtaDslManager.createSystem(inputStream);
        final XtaProcess process = system.getProcesses().get(0);
        System.out.println(
                GraphvizWriter.getInstance().writeString(XtaVisualizer.visualize(process)));
    }

    public void initXtaDslManagerTest(String filepath) {
        this.filepath = filepath;
    }
}
