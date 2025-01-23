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
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import java.util.Objects;

public final class XstsCustomTypeSymbol implements Symbol {

    private final EnumType enumType;

    private XstsCustomTypeSymbol(final EnumType enumType) {
        this.enumType = enumType;
    }

    public static XstsCustomTypeSymbol of(final EnumType xstsType) {
        return new XstsCustomTypeSymbol(xstsType);
    }

    @Override
    public int hashCode() {
        return Objects.hash(enumType);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final XstsCustomTypeSymbol that = (XstsCustomTypeSymbol) obj;
            return this.enumType.equals(that.enumType);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return enumType.toString();
    }

    @Override
    public String getName() {
        return enumType.getName();
    }

    public Type instantiate() {
        return enumType;
    }
}
