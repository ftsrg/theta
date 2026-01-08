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
package hu.bme.mit.theta.solver.z3legacy;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;
import com.microsoft.z3legacy.Sort;
import com.microsoft.z3legacy.Symbol;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Type;

import static com.google.common.base.Preconditions.*;

final class Z3TypeSymbolTable {

    private final BiMap<Type, String> constToSymbol;

    public Z3TypeSymbolTable() {
        constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
    }

    public boolean definesType(final Type type) {
        return constToSymbol.containsKey(type);
    }

    public boolean definesSymbol(final String symbol) {
        return constToSymbol.inverse().containsKey(symbol);
    }

    public String getSymbol(final Type type) {
        checkArgument(
                definesType(type), "Type %s not found in symbol table", type);
        return constToSymbol.get(type);
    }

    public Type getType(final String symbol) {
        checkArgument(definesSymbol(symbol), "Symbol %s not found in symbol table", symbol);
        return constToSymbol.inverse().get(symbol);
    }

    public void put(final Type type, final String symbol) {
        checkNotNull(type);
        checkNotNull(symbol);
        checkState(!constToSymbol.containsKey(type), "Type %s not found.", type);
        constToSymbol.put(type, symbol);
    }

    public void clear() {
        constToSymbol.clear();
    }
}
