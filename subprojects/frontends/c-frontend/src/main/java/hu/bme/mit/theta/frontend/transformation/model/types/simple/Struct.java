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

import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;

import java.util.LinkedHashMap;
import java.util.Map;

public class Struct extends NamedType {

    private final Map<String, CSimpleType> fields;
    private final String name;
    private boolean currentlyBeingBuilt;
    private static final Map<String, Struct> definedTypes = new LinkedHashMap<>();

    public static Struct getByName(String name) {
        return definedTypes.get(name);
    }

    Struct(String name, ParseContext parseContext) {
        super(parseContext, "struct");
        fields = new LinkedHashMap<>();
        this.name = name;
        if (name != null) {
            definedTypes.put(name, this);
        }
        currentlyBeingBuilt = false;
    }

    public void addField(String name, CSimpleType type) {
        fields.put(name, type);
    }

    @Override
    public CComplexType getActualType() {
        if (currentlyBeingBuilt) {
            System.err.println("WARNING: self-embedded structs! Using long as a placeholder");
            return CComplexType.getSignedInt(parseContext);
        }
        currentlyBeingBuilt = true;
        Map<String, CComplexType> actualFields = new LinkedHashMap<>();
        fields.forEach((s, cSimpleType) -> actualFields.put(s, cSimpleType.getActualType()));
        currentlyBeingBuilt = false;
        return new CStruct(this, actualFields, parseContext);
    }

    @Override
    public CSimpleType getBaseType() {
        return this;
    }

    @Override
    public boolean isVoid() {
        return false;
    }

    @Override
    public CSimpleType copyOf() {
        Struct struct = new Struct(name, parseContext);
        struct.fields.putAll(fields);
        return struct;
    }
}

