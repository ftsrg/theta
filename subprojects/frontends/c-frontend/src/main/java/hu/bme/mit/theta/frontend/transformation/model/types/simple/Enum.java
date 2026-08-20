/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

public class Enum extends CSimpleType {

    private final String id;
    private final Map<String, Optional<Expr<?>>> fields;

    /**
     * Global registry of enumeration-constant values, keyed by enumerator name. C enumerators are
     * ordinary integer constants usable anywhere an expression is expected, but the frontend models
     * an enum as a plain {@code int}, so the enumerator names would otherwise be unresolvable. This
     * registry lets the expression visitor fold an enumerator reference to its integer value. Like
     * {@code Struct}'s type registry, entries accumulate per process; this is harmless because each
     * input file is parsed in its own process (a re-parse of the same file re-registers identical
     * values).
     */
    private static final Map<String, Long> definedConstants = new LinkedHashMap<>();

    public static Long getConstantValue(String name) {
        return definedConstants.get(name);
    }

    public static void defineConstant(String name, long value) {
        definedConstants.put(name, value);
    }

    Enum(String id, Map<String, Optional<Expr<?>>> fields) {
        this.fields = fields;
        this.id = id;
    }

    public Map<String, Optional<Expr<?>>> getFields() {
        return fields;
    }

    public String getId() {
        return id;
    }

    @Override
    protected CSimpleType patch(CSimpleType cSimpleType) {
        throw new RuntimeException("Should not be here! Cannot patch with an enum.");
    }

    @Override
    public CSimpleType getBaseType() {
        Enum anEnum = new Enum(id, fields);
        anEnum.setAtomic(this.isAtomic());
        anEnum.setExtern(this.isExtern());
        anEnum.setTypedef(this.isTypedef());
        anEnum.setVolatile(this.isVolatile());
        return anEnum;
    }

    @Override
    public CSimpleType copyOf() {
        CSimpleType declaredNameRet = new Enum(id, new LinkedHashMap<>(fields));
        setUpCopy(declaredNameRet);
        return declaredNameRet;
    }
}
