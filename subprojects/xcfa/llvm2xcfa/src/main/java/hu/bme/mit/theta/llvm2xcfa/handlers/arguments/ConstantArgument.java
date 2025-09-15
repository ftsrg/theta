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
package hu.bme.mit.theta.llvm2xcfa.handlers.arguments;

import static hu.bme.mit.theta.llvm2xcfa.Utils.createConstant;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import java.util.Map;

public class ConstantArgument extends Argument {
    private final LitExpr<?> expr;

    ConstantArgument(String type, String name) {
        this.expr = createConstant(type + " " + name);
    }

    @Override
    public Type getType() {
        return expr.getType();
    }

    @Override
    public Expr<?> getExpr(Map<String, Expr<?>> values) {
        return expr;
    }

    @Override
    public String getName() {
        return expr.toString();
    }
}
