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
package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.VariableDeclarationContext;

import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.Decls.Var;

public class XstsVariableSymbol implements Symbol {

    private final String name;
    private final XstsType type;
    final Map<VarDecl<?>, hu.bme.mit.theta.xsts.type.XstsType<?>> varToType;

    public XstsVariableSymbol(final SymbolTable typeTable,
                              final Map<VarDecl<?>, hu.bme.mit.theta.xsts.type.XstsType<?>> varToType,
                              final VariableDeclarationContext context) {
        checkNotNull(context);
        name = context.name.getText();
        this.varToType = varToType;
        type = new XstsType(typeTable, context.ttype);
    }

    @Override
    public String getName() {
        return name;
    }

    public VarDecl<?> instantiate(Env env) {
        final hu.bme.mit.theta.xsts.type.XstsType<?> xstsType = type.instantiate(env);
        final VarDecl<?> var = Var(name, xstsType.getType());
        varToType.put(var, xstsType);
        return var;
    }
}
