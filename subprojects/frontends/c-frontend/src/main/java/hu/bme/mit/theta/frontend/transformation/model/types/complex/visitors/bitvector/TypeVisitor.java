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

package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Signed;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CLongDouble;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class TypeVisitor extends CComplexType.CComplexTypeVisitor<Void, Type> {
    private final ParseContext parseContext;

    public TypeVisitor(ParseContext parseContext) {
        this.parseContext = parseContext;
    }

    @Override
    public Type visit(CDouble type, Void param) {
        return FpType.of(
                parseContext.getArchitecture().getBitWidth("double_e"),
                parseContext.getArchitecture().getBitWidth("double_s"));
    }

    @Override
    public Type visit(CFloat type, Void param) {
        return FpType.of(
                parseContext.getArchitecture().getBitWidth("float_e"),
                parseContext.getArchitecture().getBitWidth("float_s"));
    }

    @Override
    public Type visit(CLongDouble type, Void param) {
        return FpType.of(
                parseContext.getArchitecture().getBitWidth("longdouble_e"),
                parseContext.getArchitecture().getBitWidth("longdouble_s"));
    }

    @Override
    public Type visit(CArray type, Void param) {
        return ArrayType.of(CComplexType.getUnsignedLong(parseContext).getSmtType(),
                type.getEmbeddedType().getSmtType());
    }

    @Override
    public Type visit(CInteger type, Void param) {
        return BvType.of(type.width(), type instanceof Signed);
    }

    @Override
    public Type visit(CVoid type, Void param) {
        return BvType.of(1, false);
    }

    @Override
    public Type visit(CStruct type, Void param) {
        return Bool();
    }
}
