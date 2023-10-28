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
package hu.bme.mit.theta.core.model;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;

import java.util.*;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.utils.PointerStore;

/**
 * Mutable implementation of a valuation.
 */
public final class MutableValuation extends Valuation {

    private final Map<Decl<?>, LitExpr<?>> declToExpr;
    private PointerStore pointerStore;

    public PointerStore getPointerStore() {
        return pointerStore;
    }

    public void setPointerStore(PointerStore pointerStore) {
        this.pointerStore = pointerStore;
    }

    public MutableValuation() {
        // LinkedHashMap is used for deterministic order
        this.declToExpr = new LinkedHashMap<>();
        this.pointerStore = new PointerStore();
    }

    public static MutableValuation copyOf(final Valuation val) {
        final MutableValuation result = new MutableValuation();
        for (final Decl<?> decl : val.getDecls()) {
            result.put(decl, val.eval(decl).get());
        }
        return result;
    }

    public MutableValuation put(final Decl<?> decl, final LitExpr<?> value) {
        checkArgument(value.getType().equals(decl.getType()), "Type mismatch.");
        declToExpr.put(decl, value);
        return this;
    }

    public MutableValuation remove(final Decl<?> decl) {
        declToExpr.remove(decl);
        return this;
    }

    public MutableValuation clear() {
        declToExpr.clear();
        return this;
    }

    public MutableValuation putAll(final Valuation val) {
        for (final Decl<?> decl : val.getDecls()) {
            declToExpr.put(decl, val.eval(decl).get());
        }
        return this;
    }

    @Override
    public Collection<Decl<?>> getDecls() {
        return Collections.unmodifiableSet(declToExpr.keySet());
    }

    @Override
    public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
        checkNotNull(decl);
        @SuppressWarnings("unchecked") final LitExpr<DeclType> val = (LitExpr<DeclType>) declToExpr.get(
                decl);
        return Optional.ofNullable(val);
    }

    @Override
    public Expr<BoolType> toExpr() {
        var valOps = SmartBoolExprs.And(declToExpr.entrySet().stream().map(e -> Eq(e.getKey().getRef(), e.getValue())).toList());
        var pointerStoreOps = pointerStore.toExpr();
        return SmartBoolExprs.And(valOps, pointerStoreOps);
    }

    @Override
    public Map<Decl<?>, LitExpr<?>> toMap() {
        return Collections.unmodifiableMap(declToExpr);
    }

}
