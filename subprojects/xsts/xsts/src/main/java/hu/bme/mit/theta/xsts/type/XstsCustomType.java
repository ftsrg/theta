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
package hu.bme.mit.theta.xsts.type;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

public final class XstsCustomType implements XstsType<EnumType> {

    private final EnumType type;

    private XstsCustomType(EnumType type) {
        this.type = type;
    }

    public static XstsCustomType of(EnumType type) {
        return new XstsCustomType(type);
    }

    public String getName() {
        return type.getName();
    }

    @Override
    public EnumType getType() {
        return type;
    }

    @Override
    public Expr<BoolType> createBoundExpr(VarDecl<EnumType> decl) {
        return Or(type.getValues().stream()
                .map(lit -> Eq(decl.getRef(), EnumLitExpr.of(type, lit)))
                .toList());
    }

    @Override
    public String serializeLiteral(LitExpr<EnumType> literal) {
        return literal.toString();
    }
}
