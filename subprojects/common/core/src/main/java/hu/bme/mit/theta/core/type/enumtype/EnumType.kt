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
package hu.bme.mit.theta.core.type.enumtype;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.theta.core.type.DomainSize;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.anytype.InvalidLitExpr;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public final class EnumType implements Equational<EnumType>, Type {

    public static final String FULLY_QUALIFIED_NAME_SEPARATOR = ".";
    private final Map<String, Integer> literals;
    private final String name;
    private int counter = 0;

    private EnumType(String name, Collection<String> values) {
        this.name = name;
        this.literals = new LinkedHashMap<>();
        values.forEach(value -> literals.put(value, counter++));
    }

    public static EnumType of(String name, Collection<String> values) {
        return new EnumType(name, values);
    }

    public static String makeLongName(String typeName, String literal) {
        return String.format("%s%s%s", typeName, FULLY_QUALIFIED_NAME_SEPARATOR, literal);
    }

    public static String makeLongName(EnumType type, String literal) {
        return makeLongName(type.getName(), literal);
    }

    public static String getShortName(String longName) {
        if (!longName.contains(FULLY_QUALIFIED_NAME_SEPARATOR)) return longName;
        return longName.substring(
                longName.indexOf(FULLY_QUALIFIED_NAME_SEPARATOR)
                        + FULLY_QUALIFIED_NAME_SEPARATOR.length());
    }

    @Override
    public DomainSize getDomainSize() {
        return DomainSize.of(literals.size());
    }

    @Override
    public EqExpr<EnumType> Eq(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
        return EnumEqExpr.of(leftOp, rightOp);
    }

    @Override
    public NeqExpr<EnumType> Neq(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
        return EnumNeqExpr.of(leftOp, rightOp);
    }

    public Set<String> getValues() {
        return literals.keySet();
    }

    public Set<String> getLongValues() {
        return literals.keySet().stream()
                .map(val -> makeLongName(this, val))
                .collect(Collectors.toSet());
    }

    public String getName() {
        return name;
    }

    public int getIntValue(EnumLitExpr literal) {
        return getIntValue(literal.getValue());
    }

    public int getIntValue(String literal) {
        checkArgument(
                literals.containsKey(literal),
                String.format("Enum type %s does not contain literal '%s'", name, literal));
        return literals.get(literal);
    }

    public LitExpr<EnumType> litFromShortName(String shortName) {
        try {
            return EnumLitExpr.of(this, shortName);
        } catch (Exception e) {
            throw new RuntimeException(
                    String.format("%s is not valid for type %s", shortName, name), e);
        }
    }

    public LitExpr<EnumType> litFromLongName(String longName) {
        if (!longName.contains(FULLY_QUALIFIED_NAME_SEPARATOR))
            throw new RuntimeException(String.format("%s is an invalid enum longname"));
        String[] parts = longName.split(Pattern.quote(FULLY_QUALIFIED_NAME_SEPARATOR));
        String type = parts[0];
        checkArgument(
                name.equals(type), String.format("%s does not belong to type %s", type, name));
        return litFromShortName(parts[1]);
    }

    public LitExpr<EnumType> litFromIntValue(int value) {
        for (Map.Entry<String, Integer> entry : literals.entrySet()) {
            if (entry.getValue() == value) {
                return EnumLitExpr.of(this, entry.getKey());
            }
        }
        return new InvalidLitExpr<>(this);
    }

    @Override
    public String toString() {
        return String.format("EnumType{%s}", name);
    }
}
