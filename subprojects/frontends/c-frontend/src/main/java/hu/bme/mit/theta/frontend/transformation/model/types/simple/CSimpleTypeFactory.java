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

package hu.bme.mit.theta.frontend.transformation.model.types.simple;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.ParseContext;

import java.util.Map;
import java.util.Optional;

public class CSimpleTypeFactory {

    public static Unsigned Unsigned() {
        return Unsigned.instance;
    }

    public static Signed Signed() {
        return Signed.instance;
    }

    public static Volatile Volatile() {
        return Volatile.instance;
    }

    public static Atomic Atomic() {
        return Atomic.instance;
    }

    public static Extern Extern() {
        return Extern.instance;
    }

    public static Typedef Typedef() {
        return Typedef.instance;
    }

    public static NamedType NamedType(final String namedType, ParseContext parseContext) {
        return new NamedType(parseContext, namedType);
    }

    public static DeclaredName DeclaredName(final String declaredName) {
        return new DeclaredName(declaredName);
    }

    public static Enum Enum(final String id, final Map<String, Optional<Expr<?>>> fields) {
        return new Enum(id, fields);
    }

    public static Struct Struct(final String name, ParseContext parseContext) {
        return new Struct(name, parseContext);
    }

    public static ThreadLocal ThreadLocal() {
        return ThreadLocal.instance;
    }
}
