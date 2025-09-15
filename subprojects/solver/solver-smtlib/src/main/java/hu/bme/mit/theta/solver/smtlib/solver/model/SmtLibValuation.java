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
package hu.bme.mit.theta.solver.smtlib.solver.model;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;
import java.util.*;

public final class SmtLibValuation extends Valuation {

    private final SmtLibSymbolTable symbolTable;
    private final SmtLibTransformationManager transformationManager;
    private final SmtLibTermTransformer termTransformer;

    private final SmtLibModel model;
    private final Map<Decl<?>, LitExpr<?>> constToExpr;
    private volatile Collection<ConstDecl<?>> constDecls = null;

    public SmtLibValuation(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer,
            final SmtLibModel model) {
        this.symbolTable = symbolTable;
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;
        this.model = model;
        constToExpr = new HashMap<>();
    }

    @Override
    public Collection<? extends Decl<?>> getDecls() {
        Collection<ConstDecl<?>> result = constDecls;
        if (result == null) {
            result = constDeclsOf(model);
            constDecls = result;
        }
        return result;
    }

    @Override
    public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(Decl<DeclType> decl) {
        checkNotNull(decl);

        if (!(decl instanceof ConstDecl)) {
            return Optional.empty();
        }

        final ConstDecl<DeclType> constDecl = (ConstDecl<DeclType>) decl;

        LitExpr<?> val = constToExpr.get(constDecl);
        if (val == null) {
            val = extractLiteral(constDecl);
            if (val != null) {
                constToExpr.put(constDecl, val);
            }
        }

        @SuppressWarnings("unchecked")
        final LitExpr<DeclType> tVal = (LitExpr<DeclType>) val;
        return Optional.ofNullable(tVal);
    }

    private <DeclType extends Type> LitExpr<?> extractLiteral(final ConstDecl<DeclType> decl) {
        final String symbol = transformationManager.toSymbol(decl);
        final Type type = decl.getType();

        if (type instanceof FuncType) {
            return extractFuncLiteral(symbol, (FuncType<?, ?>) type);
        } else if (type instanceof ArrayType) {
            return extractArrayLiteral(symbol, (ArrayType<?, ?>) type);
        } else if (type instanceof BvType) {
            return extractBvConstLiteral(symbol, (BvType) type);
        } else {
            return extractConstLiteral(symbol, type);
        }
    }

    private LitExpr<?> extractFuncLiteral(final String symbol, final FuncType<?, ?> type) {
        final String term = model.getTerm(symbol);
        if (term == null) {
            return null;
        } else {
            return checkNotNull(termTransformer.toFuncLitExpr(term, type, model));
        }
    }

    private LitExpr<?> extractArrayLiteral(final String symbol, final ArrayType<?, ?> type) {
        final String term = model.getTerm(symbol);
        if (term == null) {
            return null;
        } else {
            return checkNotNull(termTransformer.toArrayLitExpr(term, type, model));
        }
    }

    private LitExpr<?> extractBvConstLiteral(final String symbol, final BvType type) {
        final String term = model.getTerm(symbol);
        if (term == null) {
            return null;
        } else {
            return checkNotNull(termTransformer.toBvLitExpr(term, type, model));
        }
    }

    private LitExpr<?> extractConstLiteral(final String symbol, final Type type) {
        final String term = model.getTerm(symbol);
        if (term == null) {
            return null;
        } else {
            return checkNotNull(termTransformer.toLitExpr(term, type, model));
        }
    }

    @Override
    public Map<Decl<?>, LitExpr<?>> toMap() {
        getDecls().forEach(this::eval);
        return Collections.unmodifiableMap(constToExpr);
    }

    private Collection<ConstDecl<?>> constDeclsOf(final SmtLibModel model) {
        final ImmutableList.Builder<ConstDecl<?>> builder = ImmutableList.builder();
        for (final var symbol : model.getDecls()) {
            if (symbolTable.definesSymbol(symbol)) {
                final ConstDecl<?> constDecl = symbolTable.getConst(symbol);
                builder.add(constDecl);
            }
        }
        return builder.build();
    }
}
