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
package hu.bme.mit.theta.xcfa.cat;

import hu.bme.mit.theta.cat.dsl.CatDslManager;
import hu.bme.mit.theta.analysis.algorithm.mcm.MCM;
import hu.bme.mit.theta.analysis.algorithm.mcm.MCMRelation;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

@RunWith(Parameterized.class)
public class ParseTest {
    @Parameterized.Parameter(0)
    public String filepath;

    @Parameterized.Parameter(1)
    public int constraintNumber;

    @Parameterized.Parameter(2)
    public Set<String> allowedPrimitives;

    @Parameterized.Parameters()
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{
                {"/syntax-test/simple.cat", 3, Set.of("po", "rf")},
                {"/syntax-test/function.cat", 2, Set.of("po", "rf")},
                {"/syntax-test/procedure.cat", 2, Set.of("po", "rf")},
                {"/syntax-test/include-test.cat", 5, Set.of("po", "rf")},
                {"/sc.cat", 2, Set.of("po", "rf", "co", "rmw", "ext", "id")},
                {"/aarch64.cat", 3, null},
                {"/ppc.cat", 5, null},
                {"/X86.cat", 3, null},
                {"/svcomp.cat", 1, null},
        });
    }

    @Test
    public void test() throws IOException {
        try {
            final MCM mcm = CatDslManager.createMCM(new File(getClass().getResource(filepath).getFile()));
            assertEquals(constraintNumber, mcm.getConstraints().size());
            Map<String, MCMRelation> relations = new LinkedHashMap<>();
            mcm.getRelations().forEach((s, mcmRelation) -> mcmRelation.collectRelations(relations));
            if (allowedPrimitives != null) {
                final Map<String, MCMRelation> primitives = relations.entrySet().stream().filter(mcmRelation -> mcmRelation.getValue().getRule() == null).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
                assertEquals(allowedPrimitives, primitives.keySet());
            }
        } catch (IOException e) {
            throw new IOException(filepath, e);
        }
    }
}
