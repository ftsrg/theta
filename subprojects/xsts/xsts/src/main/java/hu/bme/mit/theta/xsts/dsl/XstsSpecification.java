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
package hu.bme.mit.theta.xsts.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.common.dsl.*;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.ParseException;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.XstsContext;
import java.util.*;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class XstsSpecification implements DynamicScope {

    private final SymbolTable symbolTable;
    private final SymbolTable typeTable;
    private final XstsContext context;
    private final Set<String> customTypeShortNames;

    private final Pattern tempVarPattern = Pattern.compile("temp([0-9])+");

    public XstsSpecification(XstsContext context) {
        this.context = checkNotNull(context);
        this.symbolTable = new SymbolTable();
        this.typeTable = new SymbolTable();
        customTypeShortNames = Containers.createSet();
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

        final Set<VarDecl<?>> ctrlVars = Containers.createSet();
        final List<Expr<BoolType>> initExprs = new ArrayList<>();

        for (var typeDeclContext : context.typeDeclarations) {
            final String typeName = typeDeclContext.name.getText();
            final List<String> literalNames = new ArrayList<>();
            typeDeclContext.literals.forEach(litCtx -> literalNames.add(litCtx.name.getText()));
            customTypeShortNames.addAll(literalNames);
            final EnumType enumType = EnumType.of(typeName, literalNames);
            literalNames.stream()
                    .map(litName -> EnumType.makeLongName(enumType, litName))
                    .map(fullLitName -> XstsCustomLiteralSymbol.of(enumType, fullLitName))
                    .forEach(
                            symbol -> {
                                declare(symbol);
                                env.define(symbol, symbol.instantiate());
                            });

            final XstsCustomTypeSymbol typeDeclSymbol = XstsCustomTypeSymbol.of(enumType);
            typeTable.add(typeDeclSymbol);
            env.define(typeDeclSymbol, enumType);
        }

        final Set<VarDecl<?>> stateVars =
                context.variableDeclarations.stream()
                        .map(
                                varDeclContext -> {
                                    final String varName = varDeclContext.name.getText();
                                    if (tempVarPattern.matcher(varName).matches()) {
                                        throw new ParseException(
                                                varDeclContext,
                                                "Variable name '" + varName + "' is reserved!");
                                    }
                                    if (customTypeShortNames.contains(varName))
                                        throw new ParseException(
                                                varDeclContext,
                                                String.format(
                                                        "Variable name '%s' matches at least one"
                                                                + " declared enum literal",
                                                        varName));

                                    final XstsVariableSymbol symbol =
                                            new XstsVariableSymbol(typeTable, varDeclContext);
                                    declare(symbol);

                                    final VarDecl<?> var = symbol.instantiate(env);
                                    if (varDeclContext.CTRL() != null) {
                                        ctrlVars.add(var);
                                    }
                                    if (varDeclContext.initValue != null) {
                                        var scope = new BasicDynamicScope(this);
                                        if (var.getType() instanceof EnumType enumType) {
                                            env.push();
                                            enumType.getValues()
                                                    .forEach(
                                                            literal -> {
                                                                Symbol fullNameSymbol =
                                                                        resolve(
                                                                                        EnumType
                                                                                                .makeLongName(
                                                                                                        enumType,
                                                                                                        literal))
                                                                                .orElseThrow();
                                                                if (fullNameSymbol
                                                                        instanceof
                                                                        XstsCustomLiteralSymbol
                                                                                        fNameCustLitSymbol) {
                                                                    var customSymbol =
                                                                            XstsCustomLiteralSymbol
                                                                                    .copyWithName(
                                                                                            fNameCustLitSymbol,
                                                                                            literal);
                                                                    scope.declare(customSymbol);
                                                                    env.define(
                                                                            customSymbol,
                                                                            customSymbol
                                                                                    .instantiate());
                                                                } else {
                                                                    throw new IllegalArgumentException(
                                                                            String.format(
                                                                                    "%s is not a"
                                                                                        + " literal"
                                                                                        + " of type"
                                                                                        + " %s",
                                                                                    literal,
                                                                                    enumType
                                                                                            .getName()));
                                                                }
                                                            });
                                        }
                                        initExprs.add(
                                                Eq(
                                                        var.getRef(),
                                                        new XstsExpression(
                                                                        scope,
                                                                        typeTable,
                                                                        varDeclContext.initValue)
                                                                .instantiate(env)));
                                        if (var.getType() instanceof EnumType) env.pop();
                                    }
                                    env.define(symbol, var);
                                    return var;
                                })
                        .collect(Collectors.toUnmodifiableSet());

        final NonDetStmt tranSet =
                new XstsTransitionSet(this, typeTable, context.tran.transitionSet())
                        .instantiate(env);
        final NonDetStmt initSet =
                new XstsTransitionSet(this, typeTable, context.init.transitionSet())
                        .instantiate(env);
        final NonDetStmt envSet =
                new XstsTransitionSet(this, typeTable, context.env.transitionSet())
                        .instantiate(env);

        final Expr<BoolType> initFormula = ExprUtils.simplify(And(initExprs));

        final Expr<BoolType> prop =
                cast(new XstsExpression(this, typeTable, context.prop).instantiate(env), Bool());

        final Set<VarDecl<?>> localVars = Containers.createSet();
        localVars.addAll(StmtUtils.getVars(tranSet));
        localVars.addAll(StmtUtils.getVars(envSet));
        localVars.addAll(StmtUtils.getVars(initSet));
        localVars.addAll(ExprUtils.getVars(initFormula));
        localVars.addAll(ExprUtils.getVars(prop));
        localVars.removeAll(stateVars);

        return new XSTS(
                stateVars, localVars, ctrlVars, initSet, tranSet, envSet, initFormula, prop);
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
