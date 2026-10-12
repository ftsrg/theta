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
package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mod;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Pos;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.ModExpr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;
import hu.bme.mit.theta.core.type.abstracttype.PosExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall;
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
import java.math.BigInteger;

public class CastVisitor extends CComplexType.CComplexTypeVisitor<Expr<?>, Expr<?>> {
    private final ParseContext parseContext;

    public CastVisitor(ParseContext parseContext) {
        this.parseContext = parseContext;
    }

    /**
     * A cast whose value cannot change needs no modulo. A source that is never negative -- an
     * unsigned type, or a pointer, whose value is a non-negative object id -- and no wider than the
     * target already lies in the target's range, so the wraparound is a no-op. Skipping it keeps a
     * width-preserving cast transparent: a pointer cast to `unsigned long` and back stays the very
     * same expression, so a pointer routed through an integer is still recognisable as one.
     *
     * <p>A distinct {@code Pos} wrapper is returned rather than the bare operand, so that recording
     * the target type on the result (see {@code CComplexType.castTo}) does not overwrite the
     * operand's own recorded type.
     */
    private Expr<?> widthPreserving(CInteger type, Expr<?> param) {
        CComplexType source = CComplexType.getType(param, parseContext);
        if (!(source instanceof Unsigned || source instanceof CPointer)) {
            return null;
        }
        if (source.width() > type.width()) {
            return null; // narrowing: the modulo is a real truncation
        }
        if (!cannotLeaveItsRange(param)) {
            return null;
        }
        return Pos(param);
    }

    /**
     * Whether this operand's value is already inside its own type's range, so that a modulo against
     * that range would do nothing.
     *
     * <p>The modulo is not merely a truncation: for an *arithmetic result* it is what performs the
     * unsigned wraparound. `(unsigned)(UINT_MAX + 1)` must come out 0, and in the unbounded
     * integers the sum stands at 2^32 until the modulo brings it back. So only an operand that
     * cannot leave its type's range in the first place -- a variable, a literal, a pointer id;
     * anything that is not an arithmetic result -- may skip it.
     */
    private boolean cannotLeaveItsRange(Expr<?> param) {
        Expr<?> expr = param;
        while (expr instanceof PosExpr<?> pos) {
            expr = pos.getOp();
        }
        return !(expr instanceof AddExpr
                || expr instanceof SubExpr
                || expr instanceof MulExpr
                || expr instanceof DivExpr
                || expr instanceof ModExpr
                || expr instanceof NegExpr);
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

    private Expr<?> signedCast(String widthName, Expr<?> param) {
        if (!parseContext.getSignedWraparound()) {
            // signed overflow is undefined behavior before C23; without
            // --enable-signed-wraparound the value is kept as-is.
            return Pos(param);
        }
        int width = parseContext.getArchitecture().getBitWidth(widthName);
        BigInteger halfMod = BigInteger.TWO.pow(width - 1);
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        // two's complement wraparound: ((param + 2^(w-1)) mod 2^w) - 2^(w-1)
        return Sub(Mod(Add(param, Int(halfMod)), Int(upperLimit)), Int(halfMod));
    }

    @Override
    public Expr<?> visit(Fitsall type, Expr<?> param) {
        // Fitsall is Theta's internal fits-everything integer type, it never wraps.
        return Pos(param);
    }

    @Override
    public Expr<?> visit(CSignedShort type, Expr<?> param) {
        IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
        if (sameSizeExpr != null) {
            return sameSizeExpr;
        }
        return signedCast("short", param);
    }

    @Override
    public Expr<?> visit(CUnsignedShort type, Expr<?> param) {
        Expr<?> preserved = widthPreserving(type, param);
        if (preserved != null) {
            return preserved;
        }
        int width = parseContext.getArchitecture().getBitWidth("short");
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Mod(param, Int(upperLimit));
    }

    @Override
    public Expr<?> visit(CSigned128 type, Expr<?> param) {
        IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
        if (sameSizeExpr != null) {
            return sameSizeExpr;
        }
        return signedCast("__int128", param);
    }

    @Override
    public Expr<?> visit(CUnsigned128 type, Expr<?> param) {
        Expr<?> preserved = widthPreserving(type, param);
        if (preserved != null) {
            return preserved;
        }
        int width = parseContext.getArchitecture().getBitWidth("__int128");
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Mod(param, Int(upperLimit));
    }

    @Override
    public Expr<?> visit(CSignedLongLong type, Expr<?> param) {
        IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
        if (sameSizeExpr != null) {
            return sameSizeExpr;
        }
        return signedCast("longlong", param);
    }

    @Override
    public Expr<?> visit(CUnsignedLongLong type, Expr<?> param) {
        Expr<?> preserved = widthPreserving(type, param);
        if (preserved != null) {
            return preserved;
        }
        int width = parseContext.getArchitecture().getBitWidth("longlong");
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Mod(param, Int(upperLimit));
    }

    @Override
    public Expr<?> visit(CUnsignedLong type, Expr<?> param) {
        Expr<?> preserved = widthPreserving(type, param);
        if (preserved != null) {
            return preserved;
        }
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
        return signedCast("long", param);
    }

    @Override
    public Expr<?> visit(CSignedInt type, Expr<?> param) {
        IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
        if (sameSizeExpr != null) {
            return sameSizeExpr;
        }
        return signedCast("int", param);
    }

    @Override
    public Expr<?> visit(CUnsignedInt type, Expr<?> param) {
        Expr<?> preserved = widthPreserving(type, param);
        if (preserved != null) {
            return preserved;
        }
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
        return signedCast("char", param);
    }

    @Override
    public Expr<?> visit(CUnsignedChar type, Expr<?> param) {
        Expr<?> preserved = widthPreserving(type, param);
        if (preserved != null) {
            return preserved;
        }
        int width = parseContext.getArchitecture().getBitWidth("char");
        BigInteger upperLimit = BigInteger.TWO.pow(width);
        return Mod(param, Int(upperLimit));
    }

    @Override
    public Expr<?> visit(CBool type, Expr<?> param) {
        CComplexType that = CComplexType.getType(param, parseContext);
        if (that instanceof CBool) {
            return param;
        } else {
            return Ite(Eq(param, Int(0)), Int(0), Int(1));
        }
    }

    @Override
    public Expr<?> visit(CVoid type, Expr<?> param) {
        return param.withOps(param.getOps());
    }
}
