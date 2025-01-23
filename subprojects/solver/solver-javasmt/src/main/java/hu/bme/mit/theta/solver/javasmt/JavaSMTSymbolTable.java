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
package hu.bme.mit.theta.solver.javasmt;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;
import hu.bme.mit.theta.core.decl.ConstDecl;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;

final class JavaSMTSymbolTable {

    private final BiMap<ConstDecl<?>, Formula> constToSymbol;
    private final BiMap<ConstDecl<?>, FunctionDeclaration<?>> constToFuncDecl;

    public JavaSMTSymbolTable() {
        constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
        constToFuncDecl = Maps.synchronizedBiMap(HashBiMap.create());
    }

    public boolean definesConstAsFormula(final ConstDecl<?> constDecl) {
        return constToSymbol.containsKey(constDecl);
    }

    public boolean definesConstAsFunction(final ConstDecl<?> constDecl) {
        return constToFuncDecl.containsKey(constDecl);
    }

    public boolean definesSymbol(final Formula symbol) {
        return constToSymbol.inverse().containsKey(symbol);
    }

    public boolean definesSymbol(final FunctionDeclaration<?> symbol) {
        return constToFuncDecl.inverse().containsKey(symbol);
    }

    public Formula getSymbolAsFormula(final ConstDecl<?> constDecl) {
        checkArgument(
                definesConstAsFormula(constDecl),
                "Declaration %s not found in symbol table",
                constDecl);
        return constToSymbol.get(constDecl);
    }

    public FunctionDeclaration<?> getSymbolAsFunction(final ConstDecl<?> constDecl) {
        checkArgument(
                definesConstAsFunction(constDecl),
                "Declaration %s not found in symbol table",
                constDecl);
        return constToFuncDecl.get(constDecl);
    }

    public ConstDecl<?> getConst(final Formula symbol) {
        checkArgument(definesSymbol(symbol), "Symbol %s not found in symbol table", symbol);
        return constToSymbol.inverse().get(symbol);
    }

    public ConstDecl<?> getConst(final FunctionDeclaration<?> symbol) {
        checkArgument(definesSymbol(symbol), "Symbol %s not found in symbol table", symbol);
        return constToFuncDecl.inverse().get(symbol);
    }

    public void put(final ConstDecl<?> constDecl, final Formula symbol) {
        checkNotNull(constDecl);
        checkNotNull(symbol);
        checkState(!constToSymbol.containsKey(constDecl), "Constant %s not found.", constDecl);
        constToSymbol.put(constDecl, symbol);
    }

    public void put(final ConstDecl<?> constDecl, final FunctionDeclaration<?> symbol) {
        checkNotNull(constDecl);
        checkNotNull(symbol);
        checkState(!constToFuncDecl.containsKey(constDecl), "Constant %s not found.", constDecl);
        constToFuncDecl.put(constDecl, symbol);
    }

    public void clear() {
        constToSymbol.clear();
        constToFuncDecl.clear();
    }
}
