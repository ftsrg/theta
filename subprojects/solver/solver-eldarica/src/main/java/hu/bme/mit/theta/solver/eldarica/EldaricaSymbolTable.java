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
package hu.bme.mit.theta.solver.eldarica;

import static com.google.common.base.Preconditions.*;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.functype.FuncType;

public final class EldaricaSymbolTable {

    private final BiMap<ConstDecl<?>, Utils.PredTermFormula> constToSymbol;
    private boolean useBitvectors = false;

    public EldaricaSymbolTable() {
        constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
    }

    public boolean definesConst(final ConstDecl<?> constDecl) {
        return constToSymbol.containsKey(constDecl);
    }

    public boolean definesSymbol(final Utils.PredTermFormula symbol) {
        return constToSymbol.inverse().containsKey(symbol);
    }

    public Utils.PredTermFormula getSymbol(final ConstDecl<?> constDecl) {
        checkArgument(
                definesConst(constDecl), "Declaration %s not found in symbol table", constDecl);
        return constToSymbol.get(constDecl);
    }

    public ConstDecl<?> getConst(final Utils.PredTermFormula symbol) {
        checkArgument(definesSymbol(symbol), "Symbol %s not found in symbol table", symbol);
        return constToSymbol.inverse().get(symbol);
    }

    public void put(final ConstDecl<?> constDecl, final Utils.PredTermFormula symbol) {
        checkNotNull(constDecl);
        checkNotNull(symbol);
        checkState(!constToSymbol.containsKey(constDecl), "Constant %s not found.", constDecl);
        constToSymbol.put(constDecl, symbol);
        if (!useBitvectors && anyBitvectors(constDecl.getType())) {
            useBitvectors = true;
        }
    }

    private boolean anyBitvectors(Type type) {
        if (type instanceof FuncType<?, ?> funcType) {
            return anyBitvectors(funcType.getParamType())
                    || anyBitvectors(funcType.getResultType());
        } else if (type instanceof ArrayType<?, ?> arrayType) {
            return anyBitvectors(arrayType.getElemType())
                    || anyBitvectors(arrayType.getIndexType());
        } else {
            return type instanceof BvType;
        }
    }

    public void clear() {
        constToSymbol.clear();
    }
}
