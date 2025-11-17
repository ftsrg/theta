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
package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector;

import static hu.bme.mit.theta.core.type.fptype.FpExprs.FromBv;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.ToFp;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvSignChangeExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpExprs;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Signed;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Unsigned;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.c128.CSigned128;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.c128.CUnsigned128;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cbool.CBool;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CSignedChar;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CUnsignedChar;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CUnsignedInt;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CSignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CSignedLongLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CUnsignedLongLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort.CSignedShort;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort.CUnsignedShort;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CLongDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal;

public class CastVisitor extends CComplexType.CComplexTypeVisitor<Expr<?>, Expr<?>> {
    private final ParseContext parseContext;

    public CastVisitor(ParseContext parseContext) {
        this.parseContext = parseContext;
    }

    private Expr<? extends Type> handleSignedConversion(CInteger type, Expr<?> param) {
        CComplexType that = CComplexType.getType(param, parseContext);
        if (that instanceof CPointer) {
            that = CComplexType.getUnsignedLong(parseContext);
        } else if (that instanceof CVoid) {
            that = CComplexType.getType(param.getType(), parseContext);
        }
        if (that instanceof CReal) {
            //noinspection unchecked
            return FpExprs.ToBv(
                    FpRoundingMode.RTZ, // truncate
                    (Expr<FpType>) param,
                    type.width(),
                    true);
        } else if (that instanceof CInteger) {
            if (that.width() < type.width()) {
                if (that instanceof Unsigned) {
                    return BvExprs.ZExt(
                            cast(param, BvType.of(that.width())), BvType.of(type.width(), true));
                }
                return BvExprs.SExt(
                        cast(param, BvType.of(that.width())), BvType.of(type.width(), true));
            } else if (that.width() > type.width()) {
                return BvExprs.Extract(
                        cast(param, BvType.of(that.width())), Int(0), Int(type.width()));
            } else { // width equals
                if (that instanceof Unsigned) {
                    return BvSignChangeExpr.of(
                            (Expr<BvType>) param,
                            BvType.of(((BvType) param.getType()).getSize(), true));
                } else {
                    return param;
                }
            }
        } else {
            throw new UnsupportedFrontendElementException(
                    "Compound types are not directly supported!");
        }
    }

    private Expr<? extends Type> handleUnsignedConversion(CInteger type, Expr<?> param) {
        CComplexType that = CComplexType.getType(param, parseContext);
        if (that instanceof CPointer) {
            that = CComplexType.getUnsignedLong(parseContext);
        }
        if (that instanceof CReal) {
            //noinspection unchecked
            return FpExprs.ToBv(
                    FpRoundingMode.RTZ, // truncate()
                    (Expr<FpType>) param,
                    type.width(),
                    false);
        } else if (that instanceof CInteger) {
            if (that.width() < type.width()) {
                if (that instanceof Signed) {
                    return BvExprs.SExt(
                            cast(param, BvType.of(that.width())), BvType.of(type.width(), false));
                }
                return BvExprs.ZExt(
                        cast(param, BvType.of(that.width())), BvType.of(type.width(), false));
            } else if (that.width() > type.width()) {
                return BvExprs.Extract(
                        cast(param, BvType.of(that.width())), Int(0), Int(type.width()));
            } else { // width equals
                if (that instanceof Signed) {
                    return BvSignChangeExpr.of(
                            (Expr<BvType>) param,
                            BvType.of(((BvType) param.getType()).getSize(), false));
                } else {
                    return param;
                }
            }
        } else {
            throw new UnsupportedFrontendElementException(
                    "Compound types are not directly supported!");
        }
    }

    private Expr<FpType> handleFp(CReal type, Expr<?> param) {
        CComplexType that = CComplexType.getType(param, parseContext);
        if (that instanceof CReal) {
            FpType fpType = (FpType) type.getSmtType();
            //noinspection unchecked
            return ToFp(
                    FpRoundingMode.getDefaultRoundingMode(),
                    (Expr<FpType>) param,
                    fpType.getExponent(),
                    fpType.getSignificand());
        } else if (that instanceof CInteger) {
            boolean signed = that instanceof Signed;
            //noinspection unchecked
            return FromBv(
                    FpRoundingMode.getDefaultRoundingMode(),
                    (Expr<BvType>) param,
                    (FpType) type.getSmtType(),
                    signed);
        } else {
            throw new UnsupportedOperationException("Bad type!");
        }
    }

    @Override
    public Expr<?> visit(CSignedShort type, Expr<?> param) {
        return handleSignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CUnsignedShort type, Expr<?> param) {
        return handleUnsignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(Fitsall type, Expr<?> param) {
        return handleSignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CSigned128 type, Expr<?> param) {
        return handleSignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CUnsigned128 type, Expr<?> param) {
        return handleUnsignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CSignedLongLong type, Expr<?> param) {
        return handleSignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CUnsignedLongLong type, Expr<?> param) {
        return handleUnsignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CUnsignedLong type, Expr<?> param) {
        return handleUnsignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CSignedLong type, Expr<?> param) {
        return handleSignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CSignedInt type, Expr<?> param) {
        return handleSignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CUnsignedInt type, Expr<?> param) {
        return handleUnsignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CSignedChar type, Expr<?> param) {
        return handleSignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CUnsignedChar type, Expr<?> param) {
        return handleUnsignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CBool type, Expr<?> param) {
        return handleUnsignedConversion(type, param);
    }

    @Override
    public Expr<?> visit(CVoid type, Expr<?> param) {
        return param.withOps(param.getOps());
    }

    @Override
    public Expr<?> visit(CDouble type, Expr<?> param) {
        CComplexType that = CComplexType.getType(param, parseContext);
        if (that instanceof CDouble) {
            return param.withOps(param.getOps());
        }
        return handleFp(type, param);
    }

    @Override
    public Expr<?> visit(CFloat type, Expr<?> param) {
        CComplexType that = CComplexType.getType(param, parseContext);
        if (that instanceof CFloat) {
            return param.withOps(param.getOps());
        }
        return handleFp(type, param);
    }

    @Override
    public Expr<?> visit(CLongDouble type, Expr<?> param) {
        CComplexType that = CComplexType.getType(param, parseContext);
        if (that instanceof CLongDouble) {
            return param.withOps(param.getOps());
        }
        return handleFp(type, param);
    }
}
