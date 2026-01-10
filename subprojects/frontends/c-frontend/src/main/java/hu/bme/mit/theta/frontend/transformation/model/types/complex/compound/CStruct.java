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
package hu.bme.mit.theta.frontend.transformation.model.types.complex.compound;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;

public class CStruct extends CInteger {

    private final List<Tuple2<String, CComplexType>> fields;

    public CStruct(
            CSimpleType origin,
            List<Tuple2<String, CComplexType>> fields,
            ParseContext parseContext) {
        super(origin, parseContext);
        this.fields = fields;
    }

    public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
        return visitor.visit(this, param);
    }

    @Override
    public CInteger getSignedVersion() {
        return this;
    }

    @Override
    public CInteger getUnsignedVersion() {
        return this;
    }

    public Map<String, CComplexType> getFieldsAsMap() {
        return fields.stream().collect(Collectors.toMap(Tuple2::get1, Tuple2::get2));
    }

    public List<Tuple2<String, CComplexType>> getFields() {
        return fields;
    }

    @Override
    public String getTypeName() {
        return new CUnsignedLong(null, parseContext).getTypeName();
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass()) return false;
        CStruct cStruct = (CStruct) o;
        final Function<Tuple2<String, CComplexType>, Tuple2<String, Class<?>>> mapper =
                (Tuple2<String, CComplexType> it) -> Tuple2.of(it.get1(), it.get2().getClass());
        return Objects.equals(
                fields.stream().map(mapper).toList(), cStruct.fields.stream().map(mapper).toList());
    }
}
