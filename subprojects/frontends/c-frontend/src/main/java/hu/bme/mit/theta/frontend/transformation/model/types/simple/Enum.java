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

import java.util.Map;
import java.util.Optional;

public class Enum extends CSimpleType {

    private final String id;
    private final Map<String, Optional<Expr<?>>> fields;

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
    protected void patch(CSimpleType cSimpleType) {
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
}
