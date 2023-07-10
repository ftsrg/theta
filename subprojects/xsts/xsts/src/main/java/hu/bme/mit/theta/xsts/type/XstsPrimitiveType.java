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

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public final class XstsPrimitiveType<T extends Type> implements XstsType<T> {

    private final T type;

    private XstsPrimitiveType(T type) {
        this.type = type;
    }

    public static <T extends Type> XstsPrimitiveType<T> of(T type) {
        return new XstsPrimitiveType<>(type);
    }

    @Override
    public T getType() {
        return type;
    }

    @Override
    public Expr<BoolType> createBoundExpr(VarDecl<T> decl) {
        return True();
    }

    @Override
    public String serializeLiteral(LitExpr<T> literal) {
        Preconditions.checkArgument(literal.getType().equals(type));
        return literal.toString();
    }
}
