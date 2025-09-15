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

import hu.bme.mit.theta.common.dsl.DynamicScope;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import java.util.Optional;

public final class CustomTypeDeclarationUtil {

    private CustomTypeDeclarationUtil() {}

    public static void declareTypeWithShortName(
            DynamicScope currentScope, EnumType enumType, String literal, Env env) {
        Symbol fullNameSymbol =
                currentScope.resolve(EnumType.makeLongName(enumType, literal)).orElseThrow();
        if (fullNameSymbol instanceof XstsCustomLiteralSymbol fNameCustLitSymbol) {
            var customSymbol = XstsCustomLiteralSymbol.copyWithName(fNameCustLitSymbol, literal);
            Optional<? extends Symbol> optionalSymbol = currentScope.resolve(literal);
            if (optionalSymbol.isPresent()) {
                env.define(optionalSymbol.get(), customSymbol.instantiate());
            } else {
                currentScope.declare(customSymbol);
                env.define(customSymbol, customSymbol.instantiate());
            }
        } else {
            throw new IllegalArgumentException(
                    String.format("%s is not a literal of type %s", literal, enumType.getName()));
        }
    }
}
