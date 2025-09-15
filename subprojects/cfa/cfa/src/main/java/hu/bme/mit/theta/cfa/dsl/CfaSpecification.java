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
package hu.bme.mit.theta.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ProcDeclContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.SpecContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.VarDeclContext;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

final class CfaSpecification implements Scope {

    private final SymbolTable symbolTable;

    private final List<CfaVariableSymbol> variables;
    private final List<CfaProcessSymbol> processes;

    private CfaSpecification(final SpecContext context) {
        checkNotNull(context);
        symbolTable = new SymbolTable();

        variables = createVariables(context.varDecls);
        processes = createProcesses(context.procDecls);

        declareAll(variables);
        declareAll(processes);
    }

    public static CfaSpecification fromContext(final SpecContext context) {
        return new CfaSpecification(context);
    }

    ////

    public CFA instantiate() {
        final Env env = new Env();

        for (final CfaVariableSymbol variable : variables) {
            final VarDecl<?> var = variable.instantiate();
            env.define(variable, var);
        }

        final List<CfaProcessSymbol> mainProcesses =
                processes.stream().filter(CfaProcessSymbol::isMain).collect(toList());

        if (mainProcesses.isEmpty()) {
            throw new IllegalArgumentException("No main process defined");
        } else if (mainProcesses.size() > 1) {
            throw new IllegalArgumentException("More than one main process is defined");
        } else {
            final CfaProcessSymbol process = Utils.singleElementOf(mainProcesses);
            final CFA cfa = process.instantiate(env);
            return cfa;
        }
    }

    ////

    @Override
    public Optional<Scope> enclosingScope() {
        return Optional.empty();
    }

    @Override
    public Optional<Symbol> resolve(final String name) {
        return symbolTable.get(name);
    }

    ////

    private void declareAll(final Iterable<? extends Symbol> symbols) {
        symbolTable.addAll(symbols);
    }

    private List<CfaVariableSymbol> createVariables(final List<VarDeclContext> varDeclContexts) {
        final List<CfaVariableSymbol> result = new ArrayList<>();
        for (final VarDeclContext varDeclContext : varDeclContexts) {
            final CfaVariableSymbol symbol = new CfaVariableSymbol(varDeclContext);
            result.add(symbol);
        }
        return result;
    }

    private List<CfaProcessSymbol> createProcesses(final List<ProcDeclContext> procDeclContexts) {
        final List<CfaProcessSymbol> result = new ArrayList<>();
        for (final ProcDeclContext procDeclContext : procDeclContexts) {
            final CfaProcessSymbol symbol = new CfaProcessSymbol(this, procDeclContext);
            result.add(symbol);
        }
        return result;
    }
}
