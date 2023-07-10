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
package hu.bme.mit.theta.solver.smtlib.impl.generic;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public class GenericSmtLibSymbolTable implements SmtLibSymbolTable {

    private static final String problematicCharactersRegex = ":";
    private static final String problematicCharactersReplacement = "\\$";

    private final BiMap<ConstDecl<?>, String> constToSymbol;
    private final BiMap<ConstDecl<?>, String> constToDeclaration;

    public GenericSmtLibSymbolTable() {
        constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
        constToDeclaration = Maps.synchronizedBiMap(HashBiMap.create());
    }

    public GenericSmtLibSymbolTable(GenericSmtLibSymbolTable table) {
        constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
        constToSymbol.putAll(table.constToSymbol);
        constToDeclaration = Maps.synchronizedBiMap(HashBiMap.create());
        constToDeclaration.putAll(table.constToDeclaration);
    }

    @Override
    public boolean definesConst(final ConstDecl<?> constDecl) {
        return constToSymbol.containsKey(constDecl);
    }

    @Override
    public boolean definesSymbol(final String symbol) {
        return constToSymbol.inverse().containsKey(
                symbol.replaceAll(problematicCharactersRegex, problematicCharactersReplacement));
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
    public void put(final ConstDecl<?> constDecl, final String symbol, final String declaration) {
        checkNotNull(constDecl);
        checkNotNull(symbol);
        checkNotNull(declaration);
        checkState(!constToSymbol.containsKey(constDecl), "Constant not found.");
        constToSymbol.put(constDecl,
                symbol.replaceAll(problematicCharactersRegex, problematicCharactersReplacement));
        constToDeclaration.put(constDecl,
                declaration.replaceAll(problematicCharactersRegex, problematicCharactersReplacement));
    }
}
