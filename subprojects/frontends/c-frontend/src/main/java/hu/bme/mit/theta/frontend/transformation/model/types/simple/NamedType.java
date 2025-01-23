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
package hu.bme.mit.theta.frontend.transformation.model.types.simple;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
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

/** This type either represents a built-in type like int or float, or a typedef'd named type. */
public class NamedType extends CSimpleType {
    protected final ParseContext parseContext;

    private final String namedType;
    private final Logger uniqueWarningLogger;

    NamedType(ParseContext parseContext, final String namedType, Logger uniqueWarningLogger) {
        this.parseContext = parseContext;
        this.namedType = namedType;
        this.uniqueWarningLogger = uniqueWarningLogger;
    }

    @Override
    public CComplexType getActualType() {
        CComplexType type;
        switch (namedType) {
            case "char":
                if (isSigned()) {
                    type = new CSignedChar(this, parseContext);
                } else {
                    type = new CUnsignedChar(this, parseContext);
                }
                break;
            case "int":
                if (isBool()) {
                    type = new CBool(this, parseContext);
                } else if (isSigned()) {
                    if (is128()) {
                        type = new CSigned128(this, parseContext);
                    } else if (isLong()) {
                        type = new CSignedLong(this, parseContext);
                    } else if (isLongLong()) {
                        type = new CSignedLongLong(this, parseContext);
                    } else if (isShort()) {
                        type = new CSignedShort(this, parseContext);
                    } else {
                        type = new CSignedInt(this, parseContext);
                    }
                } else {
                    if (is128()) {
                        type = new CUnsigned128(this, parseContext);
                    } else if (isLong()) {
                        type = new CUnsignedLong(this, parseContext);
                    } else if (isLongLong()) {
                        type = new CUnsignedLongLong(this, parseContext);
                    } else if (isShort()) {
                        type = new CUnsignedShort(this, parseContext);
                    } else {
                        type = new CUnsignedInt(this, parseContext);
                    }
                }
                break;
            case "double":
                if (isLong()) {
                    type = new CLongDouble(this, parseContext);
                } else {
                    type = new CDouble(this, parseContext);
                }
                break;
            case "float":
                type = new CFloat(this, parseContext);
                break;
            case "void":
                type = new CVoid(this, parseContext);
                break;
            default:
                {
                    uniqueWarningLogger.write(
                            Level.INFO, "WARNING: Unknown simple type " + namedType + "\n");
                    type = new CVoid(this, parseContext);
                    break;
                }
        }
        if (isThreadLocal()) {
            type.setThreadLocal();
        }

        for (int i = 0; i < getPointerLevel(); i++) {
            type = new CPointer(this, type, parseContext);
        }
        return type;
    }

    //    public static NamedType getIntType() {
    //        NamedType namedType = new NamedType(parseContext, "int");
    //        namedType.setSigned(true);
    //        return namedType;
    //    }
    //
    //    public static NamedType getUnsignedIntType() {
    //        NamedType namedType = new NamedType(parseContext, "int");
    //        namedType.setSigned(false);
    //        return namedType;
    //    }
    //
    //    public static NamedType getBoolType() {
    //        NamedType namedType = new NamedType(parseContext, "_Bool");
    //        namedType.setSigned(false);
    //        return namedType;
    //    }

    public String getNamedType() {
        return namedType;
    }

    @Override
    protected void patch(CSimpleType cSimpleType) {
        switch (namedType) {
            case "__int128":
                cSimpleType.set128(true);
                break;
            case "long":
                if (cSimpleType.isLong()) {
                    cSimpleType.setLongLong(true);
                    cSimpleType.setLong(false);
                } else {
                    cSimpleType.setLong(true);
                }
                break;
            case "short":
                cSimpleType.setShort(true);
                break;
            case "_Bool":
                cSimpleType.setBool(true);
                break;
            case "int":
                break;
            default:
                if (!cSimpleType.isTypedef()) {
                    throw new UnsupportedFrontendElementException(
                            "namedType should be short or long or type specifier, instead it is "
                                    + namedType);
                }
                break;
        }
    }

    @Override
    public CSimpleType getBaseType() {
        NamedType namedType = new NamedType(parseContext, getNamedType(), uniqueWarningLogger);
        namedType.setAtomic(this.isAtomic());
        namedType.setExtern(this.isExtern());
        namedType.setTypedef(this.isTypedef());
        namedType.setVolatile(this.isVolatile());
        namedType.setSigned(this.isSigned());
        namedType.setShort(this.isShort());
        namedType.setBool(this.isBool());
        namedType.setLong(this.isLong());
        namedType.setLongLong(this.isLongLong());
        namedType.set128(this.is128());

        return namedType;
    }

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();
        if (isTypedef()) {
            stringBuilder.append("typedef ");
        }
        if (isExtern()) {
            stringBuilder.append("extern ");
        }
        if (isVolatile()) {
            stringBuilder.append("volatile ");
        }
        if (isAtomic()) {
            stringBuilder.append("_Atomic ");
        }
        if (!isSigned()) {
            stringBuilder.append("unsigned ");
        }
        if (isShort()) {
            stringBuilder.append("short ");
        }
        if (isLong()) {
            stringBuilder.append("long ");
        }
        if (isBool()) {
            stringBuilder.append("_Bool ");
        }
        if (isLongLong()) {
            stringBuilder.append("long long ");
        }

        if (is128()) {
            stringBuilder.append("__int128");
        } else {
            stringBuilder.append(namedType);
        }

        return stringBuilder.toString();
    }

    @Override
    public boolean isVoid() {
        return namedType.equals("void") && getPointerLevel() == 0;
    }

    @Override
    public CSimpleType copyOf() {
        CSimpleType namedType = new NamedType(parseContext, getNamedType(), uniqueWarningLogger);
        setUpCopy(namedType);
        return namedType;
    }
}
