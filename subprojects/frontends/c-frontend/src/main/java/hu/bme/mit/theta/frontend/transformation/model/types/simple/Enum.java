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
package hu.bme.mit.theta.frontend.transformation.model.types.simple;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import java.math.BigInteger;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * An enumeration specifier. Its type is the one GCC picks ({@link #gccType}); a specifier whose
 * values could not all be computed has none, and naming it as a type is refused.
 *
 * <p>The enumeration constants and the tags of defined enumerations are kept in static registries,
 * cleared at the start of each compilation unit like {@code Struct}'s, as one JVM may parse several
 * times (see {@link #resetRegistry()}).
 */
public class Enum extends CSimpleType {

    /** The integer types GCC chooses an enumeration's type from. */
    public enum IntegerType {
        INT("int", true),
        UNSIGNED_INT("int", false),
        LONG("long", true),
        UNSIGNED_LONG("long", false),
        LONG_LONG("longlong", true),
        UNSIGNED_LONG_LONG("longlong", false);

        private final String widthName;
        private final boolean signed;

        IntegerType(String widthName, boolean signed) {
            this.widthName = widthName;
            this.signed = signed;
        }

        public boolean holds(BigInteger value, ArchitectureType architecture) {
            final int width = architecture.getBitWidth(widthName);
            final BigInteger min =
                    signed ? BigInteger.ONE.shiftLeft(width - 1).negate() : BigInteger.ZERO;
            final BigInteger max =
                    BigInteger.ONE.shiftLeft(signed ? width - 1 : width).subtract(BigInteger.ONE);
            return value.compareTo(min) >= 0 && value.compareTo(max) <= 0;
        }

        public CComplexType complexType(ParseContext parseContext) {
            return switch (this) {
                case INT -> CComplexType.getSignedInt(parseContext);
                case UNSIGNED_INT -> CComplexType.getUnsignedInt(parseContext);
                case LONG -> CComplexType.getSignedLong(parseContext);
                case UNSIGNED_LONG -> CComplexType.getUnsignedLong(parseContext);
                case LONG_LONG -> CComplexType.getSignedLongLong(parseContext);
                case UNSIGNED_LONG_LONG -> CComplexType.getUnsignedLongLong(parseContext);
            };
        }

        NamedType namedType(ParseContext parseContext, Logger uniqueWarningLogger) {
            final NamedType type = new NamedType(parseContext, "int", uniqueWarningLogger);
            type.setSigned(signed);
            if (widthName.equals("long")) {
                type.setLong(true);
            } else if (widthName.equals("longlong")) {
                type.setLongLong(true);
            }
            return type;
        }
    }

    /** An enumeration constant; a null value means it could not be computed. */
    public record Constant(BigInteger value, IntegerType type) {}

    /** The name {@link NamedType} refuses to resolve: an enumeration of unknown type. */
    static final String UNKNOWN_TYPE_NAME = "__theta_enum_of_unknown_type";

    private static final Map<String, Constant> definedConstants = new LinkedHashMap<>();
    private static final Map<String, Enum> definedTags = new LinkedHashMap<>();

    public static void resetRegistry() {
        definedConstants.clear();
        definedTags.clear();
    }

    public static Constant getConstant(String name) {
        return definedConstants.get(name);
    }

    public static void defineConstant(String name, Constant constant) {
        definedConstants.put(name, constant);
    }

    /** The definition of `enum [tag]`, or null if none has been seen. */
    public static Enum getDefinition(String tag) {
        return definedTags.get(tag);
    }

    /**
     * GCC's type for an enumeration with [values]: while they all fit `int`, `unsigned int` if none
     * is negative and `int` otherwise; beyond that, the narrowest of `unsigned int`, `unsigned
     * long` and `unsigned long long` (`int`, `long` and `long long` with a negative value) holding
     * them all. Null when no type holds them.
     */
    public static IntegerType gccType(
            Collection<BigInteger> values, ArchitectureType architecture) {
        final boolean negative = values.stream().anyMatch(value -> value.signum() < 0);
        for (IntegerType type : IntegerType.values()) {
            if (type.signed == negative
                    && values.stream().allMatch(value -> type.holds(value, architecture))) {
                return type;
            }
        }
        return null;
    }

    /**
     * GCC gives the constants `int` while every value fits it, and the enumeration's type if not.
     */
    public static IntegerType constantType(
            Collection<BigInteger> values, IntegerType enumType, ArchitectureType architecture) {
        return values.stream().allMatch(value -> IntegerType.INT.holds(value, architecture))
                ? IntegerType.INT
                : enumType;
    }

    private final String id;
    private final List<String> names;
    private final IntegerType type;

    Enum(String id, List<String> names, IntegerType type) {
        this.id = id;
        this.names = names;
        this.type = type;
    }

    /** Registers this definition under its tag, so `enum tag` resolves to its type. */
    public void defineTag() {
        if (id != null) {
            definedTags.put(id, this);
        }
    }

    public List<String> getNames() {
        return names;
    }

    public String getId() {
        return id;
    }

    /** The type this enumeration stands for wherever it names a type. */
    public NamedType underlyingType(ParseContext parseContext, Logger uniqueWarningLogger) {
        if (type == null) {
            return new NamedType(parseContext, UNKNOWN_TYPE_NAME, uniqueWarningLogger);
        }
        return type.namedType(parseContext, uniqueWarningLogger);
    }

    @Override
    protected CSimpleType patch(CSimpleType cSimpleType) {
        throw new RuntimeException("Should not be here! Cannot patch with an enum.");
    }

    @Override
    public CSimpleType getBaseType() {
        Enum anEnum = new Enum(id, names, type);
        anEnum.setAtomic(this.isAtomic());
        anEnum.setExtern(this.isExtern());
        anEnum.setStaticStorage(this.isStaticStorage());
        anEnum.setTypedef(this.isTypedef());
        anEnum.setVolatile(this.isVolatile());
        return anEnum;
    }

    @Override
    public CSimpleType copyOf() {
        CSimpleType declaredNameRet = new Enum(id, names, type);
        setUpCopy(declaredNameRet);
        return declaredNameRet;
    }
}
