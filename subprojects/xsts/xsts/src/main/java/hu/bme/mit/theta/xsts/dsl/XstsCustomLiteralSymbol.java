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
package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xsts.type.XstsCustomType;

import java.math.BigInteger;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class XstsCustomLiteralSymbol implements Symbol {

    private final XstsCustomType.XstsCustomLiteral literal;

    private static int counter = 0;

    public XstsCustomLiteralSymbol(String name) {
        this.literal = XstsCustomType.XstsCustomLiteral.of(name, BigInteger.valueOf(counter++));
    }

    @Override
    public String getName() {
        return literal.getName();
    }

    @Override
    public String toString() {
        return literal.toString();
    }

    public Expr instantiate() {
        return Int(literal.getIntValue());
    }

    public XstsCustomType.XstsCustomLiteral getLiteral() {
        return literal;
    }
}
