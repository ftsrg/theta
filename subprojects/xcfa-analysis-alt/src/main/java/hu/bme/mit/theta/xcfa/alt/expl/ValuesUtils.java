/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.expl;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.xcfa.SyntheticType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.type.SyntheticLitExpr;

import java.util.Optional;
import java.util.function.Function;

/**
 * Contains functions related to valuations.
 * More specifically, evaluating expressions and updating values.
 */
final class ValuesUtils {

    public static boolean lockable(Optional<LitExpr<SyntheticType>> x, XCFA.Process process) {
        Preconditions.checkState(x.isPresent(), "Every sync/synthetic var should be initialised");
        SyntheticLitExpr expr = (SyntheticLitExpr) x.get();
        return expr.lock(process).isValid();
    }

    public static <DeclType extends Type> Optional<LitExpr<DeclType>> eval(ExplState state, Expr<DeclType> expr) {
        Expr<DeclType> simplified = ExprUtils.simplify(PathUtils.unfold(expr, state.getIndexing()), state.getValuation());
        if (simplified instanceof LitExpr<?>) {
            return Optional.of((LitExpr<DeclType>)simplified);
        }
        return Optional.empty();
    }

    public static void executeLockOperation(MutableExplState state, VarDecl<SyntheticType> syncVar, Function<SyntheticLitExpr, SyntheticLitExpr> lockOperation) {
        var optValue = eval(state, syncVar.getRef());
        Preconditions.checkState(optValue.isPresent());
        SyntheticLitExpr sync = (SyntheticLitExpr) optValue.get();
        sync = lockOperation.apply(sync);
        if (sync.isInvalid()) {
            state.setUnsafe("Bad locking");
        }
        state.putValue(syncVar, Optional.of(sync));
    }

    public static <DeclType extends Type> void putValue(MutableExplState state, VarDecl<DeclType> var, Optional<LitExpr<DeclType>> expr) {
        if (expr.isPresent())
            state.getValuation().put(var.getConstDecl(state.getIndexing().get(var)), expr.get());
        else
            state.getValuation().remove(var.getConstDecl(state.getIndexing().get(var)));
    }

    public static void modifyIndexing(MutableExplState state, XCFA.Process.Procedure procedure, int modifier) {
        VarIndexing.Builder builder = state.getIndexing().transform();
        for (var x: procedure.getLocalVars()) {
            builder.inc(x, modifier);
        }
        for (var x: procedure.getParams()) {
            builder.inc(x, modifier);
        }
        state.setIndexing(builder.build());
    }

    /**
     * All global integers initialized to 0, all global synthetic vars initialized.
     * @return valuation with integers and synthetic vars initialized
     */
    protected static ImmutableValuation getInitialValuation(XCFA xcfa) {
        var builder = ImmutableValuation.builder();
        for (VarDecl<? extends Type> var: xcfa.getGlobalVars()) {
            IndexedConstDecl<? extends Type> x = var.getConstDecl(0);
            if (x.getType() == IntType.getInstance()) {
                builder.put(x, IntLitExpr.of(0));
            } else if (x.getType() == SyntheticType.getInstance()){
                builder.put(x, SyntheticLitExpr.unlocked());
            }
        }
        return builder.build();
    }

    protected static VarIndexing getInitialIndexing() {
        return VarIndexing.all(0);
    }

    public static boolean canExitWait(Optional<LitExpr<SyntheticType>> x, XCFA.Process process) {
        Preconditions.checkState(x.isPresent(), "Every sync/synthetic var should be initialised");
        return ((SyntheticLitExpr)x.get()).exitWait(process).isValid();
    }
}
