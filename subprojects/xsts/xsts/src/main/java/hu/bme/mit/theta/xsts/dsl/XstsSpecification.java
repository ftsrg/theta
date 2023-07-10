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

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.common.dsl.*;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.ParseException;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.XstsContext;
import hu.bme.mit.theta.xsts.type.XstsCustomType;
import hu.bme.mit.theta.xsts.type.XstsType;

import java.util.*;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class XstsSpecification implements DynamicScope {

    private final SymbolTable symbolTable;
    private final SymbolTable typeTable;
    private final XstsContext context;

    private final Pattern tempVarPattern = Pattern.compile("temp([0-9])+");

    public XstsSpecification(XstsContext context) {
        this.context = checkNotNull(context);
        this.symbolTable = new SymbolTable();
        this.typeTable = new SymbolTable();
    }

    @Override
    public Optional<? extends DynamicScope> enclosingScope() {
        return Optional.empty();
    }

    @Override
    public Optional<? extends Symbol> resolve(String name) {
        return symbolTable.get(name);
    }

    public XSTS instantiate() {
        final Env env = new Env();

        final Map<VarDecl<?>, XstsType<?>> varToType = Containers.createMap();
        final Set<VarDecl<?>> ctrlVars = Containers.createSet();
        final List<Expr<BoolType>> initExprs = new ArrayList<>();

        for (var typeDeclContext : context.typeDeclarations) {
            final List<XstsCustomLiteralSymbol> literalSymbols = new ArrayList<>();
            for (var literalContext : typeDeclContext.literals) {
                var optSymbol = resolve(literalContext.name.getText());
                if (optSymbol.isPresent()) {
                    literalSymbols.add((XstsCustomLiteralSymbol) optSymbol.get());
                } else {
                    var symbol = new XstsCustomLiteralSymbol(literalContext.name.getText());
                    literalSymbols.add(symbol);
                    declare(symbol);
                    env.define(symbol, symbol.instantiate());
                }
            }
            final List<XstsCustomType.XstsCustomLiteral> literals = literalSymbols.stream()
                    .map(XstsCustomLiteralSymbol::getLiteral).collect(Collectors.toList());
            final XstsCustomType xstsCustomType = XstsCustomType.of(typeDeclContext.name.getText(),
                    literals);

            final XstsCustomTypeSymbol typeDeclSymbol = XstsCustomTypeSymbol.of(xstsCustomType);
            typeTable.add(typeDeclSymbol);
            env.define(typeDeclSymbol, typeDeclSymbol.getXstsType());
        }

        for (var varDeclContext : context.variableDeclarations) {
            if (tempVarPattern.matcher(varDeclContext.name.getText()).matches()) {
                throw new ParseException(varDeclContext,
                        "Variable name '" + varDeclContext.name.getText() + "' is reserved!");
            }

            final XstsVariableSymbol symbol = new XstsVariableSymbol(typeTable, varToType,
                    varDeclContext);
            declare(symbol);

            final VarDecl var = symbol.instantiate(env);
            if (varDeclContext.CTRL() != null) {
                ctrlVars.add(var);
            }
            if (varDeclContext.initValue != null) {
                initExprs.add(Eq(var.getRef(),
                        new XstsExpression(this, typeTable, varDeclContext.initValue).instantiate(
                                env)));
            }
            env.define(symbol, var);
        }

        final NonDetStmt tranSet = new XstsTransitionSet(this, typeTable,
                context.tran.transitionSet(), varToType).instantiate(env);
        final NonDetStmt initSet = new XstsTransitionSet(this, typeTable,
                context.init.transitionSet(), varToType).instantiate(env);
        final NonDetStmt envSet = new XstsTransitionSet(this, typeTable,
                context.env.transitionSet(), varToType).instantiate(env);

        for (VarDecl varDecl : varToType.keySet()) {
            initExprs.add(varToType.get(varDecl).createBoundExpr(varDecl));
        }
        final Expr<BoolType> initFormula = ExprUtils.simplify(And(initExprs));

        final Expr<BoolType> prop = cast(
                new XstsExpression(this, typeTable, context.prop).instantiate(env), Bool());

        return new XSTS(varToType, ctrlVars, initSet, tranSet, envSet, initFormula, prop);
    }

    @Override
    public void declare(Symbol symbol) {
        symbolTable.add(symbol);
    }

    @Override
    public void declareAll(Collection<? extends Symbol> symbols) {
        symbolTable.addAll(symbols);
    }
}
