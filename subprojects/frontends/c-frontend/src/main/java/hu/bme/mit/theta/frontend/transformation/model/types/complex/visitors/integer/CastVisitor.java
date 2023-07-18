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

package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Unsigned;
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

import java.math.BigInteger;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mod;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Pos;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class CastVisitor extends CComplexType.CComplexTypeVisitor<Expr<?>, Expr<?>> {
    private final ParseContext parseContext;

    public CastVisitor(ParseContext parseContext) {
        this.parseContext = parseContext;
    }

    private IteExpr<?> handleUnsignedSameSize(CInteger type, Expr<?> param) {
        CComplexType that = CComplexType.getType(param, parseContext);
        if (that instanceof Unsigned && that.width() == type.width()) {
            IntLitExpr maxSigned = Int(BigInteger.TWO.pow(type.width() - 1));
            IntLitExpr maxUnsigned = Int(BigInteger.TWO.pow(type.width()));
            return Ite(Geq(param, maxSigned), Sub(param, maxUnsigned), param);
        }
        return null;
    }

    @Override
    public Expr<?> visit(Fitsall type, Expr<?> param) {
        if (true) {
            return Pos(param);
        }
        int width = parseContext.getArchitecture().getBitWidth("fitsall");
        BigInteger minValue = BigInteger.TWO.pow(width - 1).negate();
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
    }

    @Override
    public Expr<?> visit(CSignedShort type, Expr<?> param) {
        IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
        if (sameSizeExpr != null) {
            return sameSizeExpr;
        }
        if (true) {
            return Pos(param);
        }
        int width = parseContext.getArchitecture().getBitWidth("short");
        BigInteger minValue = BigInteger.TWO.pow(width - 1).negate();
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
    }

    @Override
    public Expr<?> visit(CUnsignedShort type, Expr<?> param) {
        int width = parseContext.getArchitecture().getBitWidth("short");
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Mod(param, Int(upperLimit));
    }

    @Override
    public Expr<?> visit(CSignedLongLong type, Expr<?> param) {
        IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
        if (sameSizeExpr != null) {
            return sameSizeExpr;
        }
        if (true) {
            return Pos(param);
        }
        int width = parseContext.getArchitecture().getBitWidth("longlong");
        BigInteger minValue = BigInteger.TWO.pow(width - 1).negate();
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
    }

    @Override
    public Expr<?> visit(CUnsignedLongLong type, Expr<?> param) {
        int width = parseContext.getArchitecture().getBitWidth("longlong");
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Mod(param, Int(upperLimit));
    }

    @Override
    public Expr<?> visit(CUnsignedLong type, Expr<?> param) {
        int width = parseContext.getArchitecture().getBitWidth("long");
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Mod(param, Int(upperLimit));
    }

    @Override
    public Expr<?> visit(CSignedLong type, Expr<?> param) {
        IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
        if (sameSizeExpr != null) {
            return sameSizeExpr;
        }
        if (true) {
            return Pos(param);
        }
        int width = parseContext.getArchitecture().getBitWidth("long");
        BigInteger minValue = BigInteger.TWO.pow(width - 1).negate();
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
    }

    @Override
    public Expr<?> visit(CSignedInt type, Expr<?> param) {
        IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
        if (sameSizeExpr != null) {
            return sameSizeExpr;
        }
        if (true) {
            return Pos(param);
        }
        int width = parseContext.getArchitecture().getBitWidth("int");
        BigInteger minValue = BigInteger.TWO.pow(width - 1).negate();
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
    }


    @Override
    public Expr<?> visit(CUnsignedInt type, Expr<?> param) {
        int width = parseContext.getArchitecture().getBitWidth("int");
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Mod(param, Int(upperLimit));
    }

    @Override
    public Expr<?> visit(CSignedChar type, Expr<?> param) {
        IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
        if (sameSizeExpr != null) {
            return sameSizeExpr;
        }
        if (true) {
            return Pos(param);
        }
        int width = parseContext.getArchitecture().getBitWidth("char");
        BigInteger minValue = BigInteger.TWO.pow(width - 1).negate();
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
    }

    @Override
    public Expr<?> visit(CUnsignedChar type, Expr<?> param) {
        int width = parseContext.getArchitecture().getBitWidth("char");
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Mod(param, Int(upperLimit));
    }

    @Override
    public Expr<?> visit(CBool type, Expr<?> param) {
        return Ite(Eq(param, Int(0)), Int(0), Int(1));
    }

    @Override
    public Expr<?> visit(CVoid type, Expr<?> param) {
        return param.withOps(param.getOps());
    }

    @Override
    public Expr<?> visit(CArray type, Expr<?> param) {
        checkState(CComplexType.getType(param, parseContext) instanceof CArray,
                "Only arrays can be used in place of arrays!");
        return param.withOps(param.getOps());
    }

    @Override
    public Expr<?> visit(CPointer type, Expr<?> param) {
        if (CComplexType.getType(param, parseContext) instanceof CPointer) {
            return param.withOps(param.getOps());
        }
        return visit((CUnsignedLong) CComplexType.getUnsignedLong(parseContext), param);
    }
}
