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
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.math.BigInteger;
import java.util.List;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public final class XstsCustomType implements XstsType<IntType> {

    private final String name;
    private final List<XstsCustomLiteral> literals;

    private XstsCustomType(final String name, final List<XstsCustomLiteral> literals) {
        this.name = name;
        this.literals = literals;
    }

    public static XstsCustomType of(final String name, final List<XstsCustomLiteral> literals) {
        return new XstsCustomType(name, literals);
    }

    public String getName() {
        return name;
    }

    public List<XstsCustomLiteral> getLiterals() {
        return literals;
    }

    public static final class XstsCustomLiteral {

        private final BigInteger intValue;
        private final String name;

        private XstsCustomLiteral(String name, BigInteger intValue) {
            this.name = name;
            this.intValue = intValue;
        }

        public static XstsCustomLiteral of(String name, BigInteger intValue) {
            return new XstsCustomLiteral(name, intValue);
        }

        public BigInteger getIntValue() {
            return intValue;
        }

        public String getName() {
            return name;
        }
    }

    public IntType getType() {
        return Int();
    }

    @Override
    public Expr<BoolType> createBoundExpr(VarDecl<IntType> decl) {
        return Or(literals.stream()
                .map(lit -> Eq(decl.getRef(), Int(lit.getIntValue())))
                .collect(Collectors.toList()));
    }

    @Override
    public String serializeLiteral(LitExpr<IntType> literal) {
        final IntLitExpr intLitExpr = (IntLitExpr) literal;
        final var customLiteral = literals.stream()
                .filter(lit -> lit.getIntValue().equals(intLitExpr.getValue())).findFirst();
        Preconditions.checkArgument(customLiteral.isPresent(), "Literal %s not found",
                intLitExpr.getValue());
        return customLiteral.get().getName();
    }
}
