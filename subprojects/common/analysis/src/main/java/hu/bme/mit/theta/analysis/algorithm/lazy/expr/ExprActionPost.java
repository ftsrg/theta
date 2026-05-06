package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.decl.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

import java.util.*;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public interface ExprActionPost<A extends Action> {
    BasicExprState post(final BasicExprState state, final A action);

    class QuantifiedExprActionPost<A extends ExprAction> implements ExprActionPost<A> {
        @Override
        public BasicExprState post(BasicExprState state, A action) {
            final QuantifiedPostImage post = new QuantifiedPostImage(state, action);
            final Expr<BoolType> postExpr = post.getResultExpr();
            final Collection<ParamDecl<?>> quantifiedParams = post.getQuantifiedParams();
            final Expr<BoolType> succExpr = (quantifiedParams.isEmpty()) ? postExpr : Exists(quantifiedParams, postExpr);
            return BasicExprState.of(succExpr);
        }

        private static class QuantifiedPostImage {

            private static int globalNextIndex = 100;

            private final BasicExprState state;
            private final ExprAction action;
            private Map<Decl<?>, Decl<?>> varMapping;
            private Collection<ParamDecl<?>> quantifiedParams;
            private Expr<BoolType> resultExpr;

            private QuantifiedPostImage(final BasicExprState state, final ExprAction action) {
                this.state = state;
                this.action = action;
            }

            private void setResult() {
                varMapping = new HashMap<>();
                quantifiedParams = new HashSet<>();
                final Expr<BoolType> stateExpr = state.toExpr();
                final Expr<BoolType> actionExpr = action.toExpr();
                final Expr<BoolType> indexedActionExpr = PathUtils.unfold(actionExpr, 0);
                final VarIndexing actionIndexing = action.nextIndexing();
                for (final ConstDecl<?> decl : ExprUtils.getConstants(indexedActionExpr)) {
                    assert decl instanceof IndexedConstDecl;
                    final IndexedConstDecl<?> indexedConstDecl = (IndexedConstDecl<?>) decl;
                    final VarDecl<?> varDecl = indexedConstDecl.getVarDecl();
                    final int index = indexedConstDecl.getIndex();
                    if (index == actionIndexing.get(varDecl)) {
                        varMapping.put(indexedConstDecl, varDecl);
                        if (index > 0 && !varMapping.containsKey(varDecl)) {
                            final IndexedConstDecl<?> newVarDecl = nextIndexedDecl(varDecl);
                            varMapping.put(varDecl, newVarDecl);
                            addQuantifiedParam(newVarDecl);
                        }
                    } else {
                        Decl<?> newVarDecl = varMapping.get(varDecl);
                        if (newVarDecl == null) {
                            newVarDecl = nextIndexedDecl(varDecl);
                            varMapping.put(varDecl, newVarDecl);
                            addQuantifiedParam(newVarDecl);
                        }
                        varMapping.put(indexedConstDecl, newVarDecl);
                    }
                }
                for (final ConstDecl<?> decl : ExprUtils.getConstants(stateExpr)) {
                    if (decl instanceof IndexedConstDecl && !varMapping.containsKey(decl)) {
                        final IndexedConstDecl<?> indexedConstDecl = (IndexedConstDecl<?>) decl;
                        final IndexedConstDecl<?> newVarDecl = nextIndexedDecl(indexedConstDecl.getVarDecl());
                        varMapping.put(indexedConstDecl, newVarDecl);
                        addQuantifiedParam(newVarDecl);
                    }
                }
                resultExpr = replaceVars(And(stateExpr, indexedActionExpr));
            }

            private <T extends Type> IndexedConstDecl<T> nextIndexedDecl(final VarDecl<T> decl) {
                final IndexedConstDecl<T> newDecl = decl.getConstDecl(globalNextIndex);
                globalNextIndex++;
                return newDecl;
            }

            private <T extends Type> void addQuantifiedParam(final Decl<T> decl) {
                final ParamDecl<T> quantifiedParam = Decls.Param(decl.getName(), decl.getType());
                quantifiedParams.add(quantifiedParam);
            }

            private <T extends Type> Expr<T> replaceVars(final Expr<T> expr) {
                if (expr instanceof RefExpr) {
                    final Decl<T> originalDecl = ((RefExpr<T>) expr).getDecl();
                    final Decl<?> replacementDecl = varMapping.get(originalDecl);
                    if (replacementDecl == null) {
                        return expr;
                    }
                    return cast(replacementDecl.getRef(), expr.getType());
                }
                return expr.map(this::replaceVars);
            }

            private Expr<BoolType> getResultExpr() {
                Expr<BoolType> result = resultExpr;
                if (result == null) {
                    setResult();
                    result = resultExpr;
                }
                return result;
            }

            private Collection<ParamDecl<?>> getQuantifiedParams() {
                Collection<ParamDecl<?>> result = quantifiedParams;
                if (result == null) {
                    setResult();
                    result = quantifiedParams;
                }
                return result;
            }
        }
    }


}
