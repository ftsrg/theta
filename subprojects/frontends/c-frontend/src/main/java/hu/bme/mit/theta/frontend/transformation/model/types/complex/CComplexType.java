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
package hu.bme.mit.theta.frontend.transformation.model.types.complex;

import static hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.*;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.*;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.c128.C128;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.c128.CSigned128;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.c128.CUnsigned128;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cbool.CBool;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CChar;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CSignedChar;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CUnsignedChar;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CInt;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CUnsignedInt;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CSignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CLongLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CSignedLongLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CUnsignedLongLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort.CShort;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort.CSignedShort;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort.CUnsignedShort;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CLongDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.util.List;
import java.util.Map.Entry;
import java.util.Optional;

public abstract class CComplexType {
    private final CSimpleType origin;
    private boolean threadLocal = false;
    private boolean atomic = false;

    protected final ParseContext parseContext;

    protected CComplexType(CSimpleType origin, ParseContext parseContext) {
        this.origin = origin;
        this.parseContext = parseContext;
    }

    public ParseContext getParseContext() {
        return parseContext;
    }

    public CSimpleType getOrigin() {
        return origin;
    }

    public LitExpr<?> getNullValue() {
        LitExpr<?> accept = this.accept(getNullValueVisitor(parseContext), null);
        parseContext.getMetadata().create(accept, "cType", this);
        return accept;
    }

    public LitExpr<?> getUnitValue() {
        LitExpr<?> accept = this.accept(getUnitValueVisitor(parseContext), null);
        parseContext.getMetadata().create(accept, "cType", this);
        return accept;
    }

    public LitExpr<?> getValue(String value) {
        LitExpr<?> accept = this.accept(getValueVisitor(parseContext), value);
        parseContext.getMetadata().create(accept, "cType", this);
        return accept;
    }

    public AssumeStmt limit(Expr<?> expr) {
        return this.accept(getLimitVisitor(parseContext), expr);
    }

    public Expr<?> castTo(Expr<?> expr) {
        Expr<?> accept = this.accept(getCastVisitor(parseContext), expr);
        parseContext.getMetadata().create(accept, "cType", this);
        return accept;
    }

    public Type getSmtType() {
        return this.accept(getTypeVisitor(parseContext), null);
    }

    public CComplexType getSmallestCommonType(CComplexType type) {
        throw new RuntimeException("Common type is not applicable for this type!");
    }

    public String getTypeName() {
        throw new RuntimeException("Type name could not be queried from this type: " + this);
    }

    public int width() {
        return parseContext.getArchitecture().getBitWidth(getTypeName());
    }

    public static CComplexType getSmallestCommonType(
            List<CComplexType> types, ParseContext parseContext) {
        CComplexType ret = getSignedInt(parseContext);
        for (int i = 0; i < types.size(); i++) {
            ret = ret.getSmallestCommonType(types.get(i));
        }
        return ret;
    }

    public static CComplexType getType(String s, ParseContext parseContext) {
        return switch (s) {
            case "_Bool" -> new CBool(null, parseContext);
            case "char", "signedchar" -> new CSignedChar(null, parseContext);
            case "short", "signedshort" -> new CSignedShort(null, parseContext);
            case "unsignedshort" -> new CUnsignedShort(null, parseContext);
            case "unsignedchar" -> new CUnsignedChar(null, parseContext);
            case "signed", "int", "signedint" -> new CSignedInt(null, parseContext);
            case "unsigned", "unsignedint" -> new CUnsignedInt(null, parseContext);
            case "long", "signedlong", "longint", "signedlongint" ->
                    new CSignedLong(null, parseContext);
            case "unsignedlong", "unsignedlongint" -> new CUnsignedLong(null, parseContext);
            case "longlong", "signedlonglong", "lonlongint", "signedlonglongint" ->
                    new CSignedLongLong(null, parseContext);
            case "unsignedlonglong", "unsignedlonglongint" ->
                    new CUnsignedLongLong(null, parseContext);
            case "float" -> new CFloat(null, parseContext);
            case "double" -> new CDouble(null, parseContext);
            case "longdouble" -> new CLongDouble(null, parseContext);
            default -> {
                if (s.endsWith("*")) {
                    yield new CPointer(null, null, parseContext);
                } else {
                    yield null;
                }
            }
        };
    }

    public static CComplexType getType(Expr<?> expr, ParseContext parseContext) {
        Optional<Object> cTypeOptional = parseContext.getMetadata().getMetadataValue(expr, "cType");
        if (cTypeOptional.isPresent() && cTypeOptional.get() instanceof CComplexType) {
            return (CComplexType) cTypeOptional.get();
        } else if (cTypeOptional.isPresent() && cTypeOptional.get() instanceof CSimpleType) {
            return ((CSimpleType) cTypeOptional.get()).getActualType();
        } else {
            return getType(expr.getType(), parseContext);
            //            throw new RuntimeException("Type not known for expression: " + expr);
        }
    }

    public static CComplexType getType(Type type, ParseContext parseContext) {
        if (type instanceof IntType) {
            return new CSignedInt(null, parseContext);
        } else if (type instanceof ArrayType<?, ?> aType) {
            return new CArray(null, getType(aType.getElemType(), parseContext), parseContext);
        } else if (type instanceof BoolType) {
            return new CBool(null, parseContext);
        } else if (type instanceof FpType) {
            final var doubleType =
                    FpType.of(
                            parseContext.getArchitecture().getBitWidth("double_e"),
                            parseContext.getArchitecture().getBitWidth("double_s"));
            if (doubleType.equals(type)) {
                return new CDouble(null, parseContext);
            }
            final var floatType =
                    FpType.of(
                            parseContext.getArchitecture().getBitWidth("float_e"),
                            parseContext.getArchitecture().getBitWidth("float_s"));
            if (floatType.equals(type)) {
                return new CFloat(null, parseContext);
            }
            final var longDoubleType =
                    FpType.of(
                            parseContext.getArchitecture().getBitWidth("longdouble_e"),
                            parseContext.getArchitecture().getBitWidth("longdouble_s"));
            if (longDoubleType.equals(type)) {
                return new CFloat(null, parseContext);
            }
            throw new UnsupportedFrontendElementException(
                    "No suitable size found for type: " + type);
        } else if (type instanceof BvType) {
            for (Entry<String, Integer> entry :
                    parseContext.getArchitecture().standardTypeSizes.entrySet()) {
                String s = entry.getKey();
                Integer integer = entry.getValue();
                if (integer == ((BvType) type).getSize()) {
                    switch (s) {
                        case "bool":
                            return new CBool(null, parseContext);
                        case "char":
                            return ((BvType) type).getSigned()
                                    ? new CSignedChar(null, parseContext)
                                    : new CUnsignedChar(null, parseContext);
                        case "short":
                            return ((BvType) type).getSigned()
                                    ? new CSignedShort(null, parseContext)
                                    : new CUnsignedShort(null, parseContext);
                        case "int":
                            return ((BvType) type).getSigned()
                                    ? new CSignedInt(null, parseContext)
                                    : new CUnsignedInt(null, parseContext);
                        case "long":
                            return ((BvType) type).getSigned()
                                    ? new CSignedLong(null, parseContext)
                                    : new CUnsignedLong(null, parseContext);
                        case "longlong":
                            return ((BvType) type).getSigned()
                                    ? new CSignedLongLong(null, parseContext)
                                    : new CUnsignedLongLong(null, parseContext);
                        case "__int128":
                            return ((BvType) type).getSigned()
                                    ? new CSigned128(null, parseContext)
                                    : new CUnsigned128(null, parseContext);
                    }
                }
            }
            throw new UnsupportedFrontendElementException(
                    "No suitable width found for type: " + type);
        } else {
            throw new UnsupportedFrontendElementException("Not yet implemented for type: " + type);
        }
    }

    public void setThreadLocal() {
        threadLocal = true;
    }

    public boolean isThreadLocal() {
        return threadLocal;
    }

    public void setAtomic() {
        atomic = true;
    }

    public boolean isAtomic() {
        return atomic;
    }

    public static CComplexType getSignedInt(ParseContext parseContext) {
        return new CSignedInt(null, parseContext);
    }

    public static CComplexType getUnsigned128(ParseContext parseContext) {
        return new CUnsigned128(null, parseContext);
    }

    public static CComplexType getUnsignedLongLong(ParseContext parseContext) {
        return new CUnsignedLongLong(null, parseContext);
    }

    public static CComplexType getUnsignedLong(ParseContext parseContext) {
        return new CUnsignedLong(null, parseContext);
    }

    public static CComplexType getUnsignedInt(ParseContext parseContext) {
        return new CUnsignedInt(null, parseContext);
    }

    public static CComplexType getSigned128(ParseContext parseContext) {
        return new CSigned128(null, parseContext);
    }

    public static CComplexType getSignedLongLong(ParseContext parseContext) {
        return new CSignedLongLong(null, parseContext);
    }

    public static CComplexType getSignedLong(ParseContext parseContext) {
        return new CSignedLong(null, parseContext);
    }

    public static CComplexType getFloat(ParseContext parseContext) {
        return new CFloat(null, parseContext);
    }

    public static CComplexType getDouble(ParseContext parseContext) {
        return new CDouble(null, parseContext);
    }

    public static CComplexType getLongDouble(ParseContext parseContext) {
        return new CLongDouble(null, parseContext);
    }

    public static CComplexType getFitsall(ParseContext parseContext) {
        return new Fitsall(null, parseContext);
    }

    public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
        return visitor.visit(this, param);
    }

    public static class CComplexTypeVisitor<T, R> {
        public R visit(CComplexType type, T param) {
            throw new UnsupportedFrontendElementException(
                    "Not (yet) implemented ("
                            + type.getClass().getSimpleName()
                            + " in "
                            + this.getClass().getName()
                            + ")");
        }

        public R visit(CVoid type, T param) {
            return visit(((CComplexType) type), param);
        }

        public R visit(CReal type, T param) {
            return visit(((CComplexType) type), param);
        }

        public R visit(CDouble type, T param) {
            return visit(((CReal) type), param);
        }

        public R visit(CFloat type, T param) {
            return visit(((CReal) type), param);
        }

        public R visit(CLongDouble type, T param) {
            return visit(((CReal) type), param);
        }

        public R visit(CInteger type, T param) {
            return visit(((CComplexType) type), param);
        }

        public R visit(CShort type, T param) {
            return visit(((CInteger) type), param);
        }

        public R visit(CSignedShort type, T param) {
            return visit(((CShort) type), param);
        }

        public R visit(CUnsignedShort type, T param) {
            return visit(((CShort) type), param);
        }

        public R visit(C128 type, T param) {
            return visit(((CInteger) type), param);
        }

        public R visit(CLongLong type, T param) {
            return visit(((CInteger) type), param);
        }

        public R visit(CSignedLongLong type, T param) {
            return visit(((CLongLong) type), param);
        }

        public R visit(CSigned128 type, T param) {
            return visit(((C128) type), param);
        }

        public R visit(Fitsall type, T param) {
            return visit(((CInteger) type), param);
        }

        public R visit(CUnsigned128 type, T param) {
            return visit(((C128) type), param);
        }

        public R visit(CUnsignedLongLong type, T param) {
            return visit(((CLongLong) type), param);
        }

        public R visit(CLong type, T param) {
            return visit(((CInteger) type), param);
        }

        public R visit(CUnsignedLong type, T param) {
            return visit(((CLong) type), param);
        }

        public R visit(CSignedLong type, T param) {
            return visit(((CLong) type), param);
        }

        public R visit(CInt type, T param) {
            return visit(((CInteger) type), param);
        }

        public R visit(CSignedInt type, T param) {
            return visit(((CInt) type), param);
        }

        public R visit(CUnsignedInt type, T param) {
            return visit(((CInt) type), param);
        }

        public R visit(CChar type, T param) {
            return visit(((CInteger) type), param);
        }

        public R visit(CSignedChar type, T param) {
            return visit(((CChar) type), param);
        }

        public R visit(CUnsignedChar type, T param) {
            return visit(((CChar) type), param);
        }

        public R visit(CBool type, T param) {
            return visit(((CInteger) type), param);
        }

        public R visit(CCompound type, T param) {
            return visit(((CComplexType) type), param);
        }

        public R visit(CArray type, T param) {
            return CComplexType.getUnsignedLong(type.getParseContext()).accept(this, param);
        }

        public R visit(CFunction type, T param) {
            return visit(((CCompound) type), param);
        }

        public R visit(CStruct type, T param) {
            return CComplexType.getUnsignedLong(type.getParseContext()).accept(this, param);
        }

        public R visit(CPointer type, T param) {
            return CComplexType.getUnsignedLong(type.getParseContext()).accept(this, param);
        }
    }
}
