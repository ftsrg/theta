/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.ParseContext;
import java.util.Map;

/** A loop statement: `for`, `while` or `do`-`while`. */
public abstract class CLoop extends CStatement {

    // the variables in scope where the controlling expression is evaluated, by C name
    private Map<String, VarDecl<?>> variablesAtGuard = Map.of();

    protected CLoop(ParseContext parseContext) {
        super(parseContext);
    }

    public abstract CStatement getBody();

    public abstract CStatement getGuard();

    public Map<String, VarDecl<?>> getVariablesAtGuard() {
        return variablesAtGuard;
    }

    public void setVariablesAtGuard(Map<String, VarDecl<?>> variablesAtGuard) {
        this.variablesAtGuard = variablesAtGuard;
    }
}
