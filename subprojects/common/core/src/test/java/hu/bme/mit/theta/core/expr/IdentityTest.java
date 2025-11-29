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
package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.utils.ExpressionUtils;
import java.util.Collection;
import org.junit.Assert;
import org.junit.jupiter.api.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class IdentityTest {
    @Parameter(value = 0)
    public String className;

    @Parameter(value = 1)
    public Expr<?> expr;

    @Parameters(name = "Expression {0}: {1}")
    public static Collection<Object[]> data() {
        return ExpressionUtils.AllExpressions().entrySet().stream()
                .map(e -> new Object[] {e.getKey(), e.getValue()})
                .toList();
    }

    @Test
    public void testRoundtrip() {
        Assert.assertEquals(expr.withOps(expr.getOps()), expr);
    }
}
