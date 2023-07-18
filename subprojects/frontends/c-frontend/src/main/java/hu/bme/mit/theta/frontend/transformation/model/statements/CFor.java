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

package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.frontend.ParseContext;

public class CFor extends CStatement {

    private final CStatement body;
    private final CStatement init;
    private final CStatement guard;
    private final CStatement increment;

    public CFor(CStatement body, CStatement init, CStatement guard, CStatement increment, ParseContext parseContext) {
        super(parseContext);
        this.body = body;
        this.init = init;
        this.guard = guard;
        this.increment = increment;
    }

    public CStatement getIncrement() {
        return increment;
    }

    public CStatement getGuard() {
        return guard;
    }

    public CStatement getInit() {
        return init;
    }

    public CStatement getBody() {
        return body;
    }

    @Override
    public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
        return visitor.visit(this, param);
    }
}
