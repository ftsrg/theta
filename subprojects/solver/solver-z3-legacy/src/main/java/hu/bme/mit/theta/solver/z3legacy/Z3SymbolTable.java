/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.z3legacy;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;
import hu.bme.mit.theta.core.decl.ConstDecl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

final class Z3SymbolTable {

    private final BiMap<ConstDecl<?>, com.microsoft.z3legacy.FuncDecl> constToSymbol;

    public Z3SymbolTable() {
        constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
    }

    public boolean definesConst(final ConstDecl<?> constDecl) {
        return constToSymbol.containsKey(constDecl);
    }

    public boolean definesSymbol(final com.microsoft.z3legacy.FuncDecl symbol) {
        return constToSymbol.inverse().containsKey(symbol);
    }

    public com.microsoft.z3legacy.FuncDecl getSymbol(final ConstDecl<?> constDecl) {
        checkArgument(definesConst(constDecl), "Declaration %s not found in symbol table",
                constDecl);
        return constToSymbol.get(constDecl);
    }

    public ConstDecl<?> getConst(final com.microsoft.z3legacy.FuncDecl symbol) {
        checkArgument(definesSymbol(symbol), "Symbol %s not found in symbol table", symbol);
        return constToSymbol.inverse().get(symbol);
    }

    public void put(final ConstDecl<?> constDecl, final com.microsoft.z3legacy.FuncDecl symbol) {
        checkNotNull(constDecl);
        checkNotNull(symbol);
        checkState(!constToSymbol.containsKey(constDecl), "Constant %s not found.", constDecl);
        constToSymbol.put(constDecl, symbol);
    }

    public void clear() {
        constToSymbol.clear();
    }

}
