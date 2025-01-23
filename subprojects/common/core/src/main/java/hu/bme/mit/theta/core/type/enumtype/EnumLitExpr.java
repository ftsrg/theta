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
package hu.bme.mit.theta.core.type.enumtype;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import com.google.common.base.Objects;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;

public final class EnumLitExpr extends NullaryExpr<EnumType> implements LitExpr<EnumType> {

    private final EnumType type;
    private final String value;

    private EnumLitExpr(EnumType type, String value) {
        this.type = type;
        this.value = value;
    }

    public static EnumLitExpr of(EnumType type, String literalName) {
        String value = EnumType.getShortName(literalName);
        checkArgument(
                type.getValues().contains(value),
                "Invalid value %s for type %s",
                value,
                type.getName());
        return new EnumLitExpr(type, value);
    }

    public static BoolLitExpr eq(EnumLitExpr l, EnumLitExpr r) {
        return Bool(l.type.equals(r.type) && l.value.equals(r.value));
    }

    public static BoolLitExpr neq(EnumLitExpr l, EnumLitExpr r) {
        return Bool(!l.type.equals(r.type) || !l.value.equals(r.value));
    }

    @Override
    public EnumType getType() {
        return type;
    }

    public String getValue() {
        return value;
    }

    @Override
    public LitExpr<EnumType> eval(Valuation val) {
        return this;
    }

    @Override
    public String toString() {
        return EnumType.makeLongName(type.getName(), value);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        EnumLitExpr that = (EnumLitExpr) o;
        return Objects.equal(type, that.type) && Objects.equal(value, that.value);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(type, value);
    }
}
