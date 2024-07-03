/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Signed;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CLongDouble;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.math.BigInteger;

public class NullValueVisitor extends CComplexType.CComplexTypeVisitor<Void, LitExpr<?>> {
    private final ParseContext parseContext;

    public NullValueVisitor(ParseContext parseContext) {
        this.parseContext = parseContext;
    }

    @Override
    public LitExpr<?> visit(CDouble type, Void param) {
        return FpUtils.bigFloatToFpLitExpr(
                new BigFloat(
                        "0.0",
                        new BinaryMathContext(
                                parseContext.getArchitecture().getBitWidth("double_s"),
                                parseContext.getArchitecture().getBitWidth("double_e"))),
                FpType.of(
                        parseContext.getArchitecture().getBitWidth("double_e"),
                        parseContext.getArchitecture().getBitWidth("double_s")));
    }

    @Override
    public LitExpr<?> visit(CFloat type, Void param) {
        return FpUtils.bigFloatToFpLitExpr(
                new BigFloat(
                        "0.0",
                        new BinaryMathContext(
                                parseContext.getArchitecture().getBitWidth("float_s"),
                                parseContext.getArchitecture().getBitWidth("float_e"))),
                FpType.of(
                        parseContext.getArchitecture().getBitWidth("float_e"),
                        parseContext.getArchitecture().getBitWidth("float_s")));
    }

    @Override
    public LitExpr<?> visit(CLongDouble type, Void param) {
        return FpUtils.bigFloatToFpLitExpr(
                new BigFloat(
                        "0.0",
                        new BinaryMathContext(
                                parseContext.getArchitecture().getBitWidth("longdouble_s"),
                                parseContext.getArchitecture().getBitWidth("longdouble_e"))),
                FpType.of(
                        parseContext.getArchitecture().getBitWidth("longdouble_e"),
                        parseContext.getArchitecture().getBitWidth("longdouble_s")));
    }

    @Override
    public LitExpr<?> visit(CInteger type, Void param) {
        if (type instanceof Signed) {
            return BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.ZERO, type.width());
        } else {
            return BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.ZERO, type.width());
        }
    }

}
