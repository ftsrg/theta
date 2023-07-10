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
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public final class XstsArrayType<IndexType extends Type, ElemType extends Type> implements
        XstsType<ArrayType<IndexType, ElemType>> {

    private final XstsType<IndexType> indexType;
    private final XstsType<ElemType> elemType;
    private ArrayType<IndexType, ElemType> type;

    private XstsArrayType(XstsType<IndexType> indexType, XstsType<ElemType> elemType) {
        this.indexType = indexType;
        this.elemType = elemType;
        this.type = Array(indexType.getType(), elemType.getType());
    }

    public static <IndexType extends Type, ElemType extends Type> XstsArrayType<IndexType, ElemType> of(
            XstsType<IndexType> indexType, XstsType<ElemType> elemType) {
        return new XstsArrayType<>(indexType, elemType);
    }

    public ArrayType<IndexType, ElemType> getType() {
        return type;
    }

    @Override
    public Expr<BoolType> createBoundExpr(VarDecl<ArrayType<IndexType, ElemType>> decl) {
        return True();
    }

    @Override
    public String serializeLiteral(LitExpr<ArrayType<IndexType, ElemType>> literal) {
        Preconditions.checkArgument(literal.getType().equals(type));
        final ArrayLitExpr<IndexType, ElemType> arrayLitExpr = (ArrayLitExpr<IndexType, ElemType>) literal;
        return Utils.lispStringBuilder("array")
                .addAll(arrayLitExpr.getElements().stream().map(
                        elem -> String.format("(%s %s)", indexType.serializeLiteral(elem.get1()),
                                elemType.serializeLiteral(elem.get2()))))
                .add((String.format("(default %s)",
                        elemType.serializeLiteral(arrayLitExpr.getElseElem()))))
                .toString();
    }
}
