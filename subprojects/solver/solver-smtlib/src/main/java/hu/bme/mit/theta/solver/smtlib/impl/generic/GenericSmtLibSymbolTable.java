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
package hu.bme.mit.theta.solver.smtlib.impl.generic;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Pattern;

public class GenericSmtLibSymbolTable implements SmtLibSymbolTable {

    static final Pattern problematicCharactersRegex = Pattern.compile("[:#]");

    public static String encodeSymbol(String name) {
        if (problematicCharactersRegex.matcher(name).find()) {
            char[] chars = name.toCharArray();
            if (chars[0] == '|' && chars[chars.length - 1] == '|') {
                return name;
            } else {
                return "|%s|".formatted(name);
            }
        } else {
            return name;
        }
    }

    private final BiMap<ConstDecl<?>, String> constToSymbol;
    private final BiMap<ConstDecl<?>, String> constToDeclaration;
    private final Map<String, EnumLitExpr> symbolToEnumLiteral;

    public GenericSmtLibSymbolTable() {
        constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
        constToDeclaration = Maps.synchronizedBiMap(HashBiMap.create());
        symbolToEnumLiteral = new HashMap<>();
    }

    public GenericSmtLibSymbolTable(GenericSmtLibSymbolTable table) {
        constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
        constToSymbol.putAll(table.constToSymbol);
        constToDeclaration = Maps.synchronizedBiMap(HashBiMap.create());
        constToDeclaration.putAll(table.constToDeclaration);
        symbolToEnumLiteral = new HashMap<>();
        symbolToEnumLiteral.putAll(table.symbolToEnumLiteral);
    }

    @Override
    public boolean definesConst(final ConstDecl<?> constDecl) {
        return constToSymbol.containsKey(constDecl);
    }

    @Override
    public boolean definesSymbol(final String symbol) {
        return constToSymbol.inverse().containsKey(symbol);
    }

    @Override
    public boolean definesEnumLiteral(String literal) {
        return symbolToEnumLiteral.containsKey(literal);
    }

    @Override
    public String getSymbol(final ConstDecl<?> constDecl) {
        checkArgument(definesConst(constDecl));
        return constToSymbol.get(constDecl);
    }

    @Override
    public String getDeclaration(final ConstDecl<?> constDecl) {
        checkArgument(definesConst(constDecl));
        return constToDeclaration.get(constDecl);
    }

    @Override
    public ConstDecl<?> getConst(final String symbol) {
        checkArgument(definesSymbol(symbol));
        return constToSymbol.inverse().get(symbol);
    }

    @Override
    public EnumLitExpr getEnumLiteral(String literal) {
        return symbolToEnumLiteral.get(literal);
    }

    @Override
    public void put(final ConstDecl<?> constDecl, final String symbol, final String declaration) {
        checkNotNull(constDecl);
        checkNotNull(symbol);
        checkNotNull(declaration);
        checkState(!constToSymbol.containsKey(constDecl), "Constant not found.");
        constToSymbol.put(constDecl, symbol);
        constToDeclaration.put(constDecl, declaration);
    }

    @Override
    public void putEnumLiteral(String symbol, EnumLitExpr litExpr) {
        symbolToEnumLiteral.put(symbol, litExpr);
    }
}
