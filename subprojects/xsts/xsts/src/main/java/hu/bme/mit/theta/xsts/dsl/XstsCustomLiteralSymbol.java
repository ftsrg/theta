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
package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;

public class XstsCustomLiteralSymbol implements Symbol {

    private final EnumType type;

    private final String literal;

    public XstsCustomLiteralSymbol(EnumType type, String literal) {
        this.type = type;
        this.literal = literal;
    }

    public static XstsCustomLiteralSymbol of(EnumType type, String literal) {
        return new XstsCustomLiteralSymbol(type, literal);
    }

    @Override
    public String getName() {
        return literal;
    }

    @Override
    public String toString() {
        return literal;
    }

    public Expr instantiate() {
        return EnumLitExpr.of(type, EnumType.getShortName(literal));
    }

    public static XstsCustomLiteralSymbol copyWithName(
            XstsCustomLiteralSymbol symbol, String newName) {
        return new XstsCustomLiteralSymbol(symbol.type, newName);
    }
}
