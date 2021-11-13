/*
 *  Copyright 2021 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.utils;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.LoopStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.OrtStmt;
import hu.bme.mit.theta.core.stmt.PopStmt;
import hu.bme.mit.theta.core.stmt.PushStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.indexings.PushPopVarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

final class StmtToExprTransformer {
    private StmtToExprTransformer() {
    }

    static StmtUnfoldResult toExpr(final Stmt stmt, final VarIndexing indexing) {
        return stmt.accept(StmtToExprVisitor.INSTANCE, indexing);
    }

    static StmtUnfoldResult toExpr(final List<? extends Stmt> stmts, final VarIndexing indexing) {
        final Collection<Expr<BoolType>> resultExprs = new ArrayList<>();
        VarIndexing resultIndexing = indexing;

        for (final Stmt stmt : stmts) {
            final StmtUnfoldResult subResult = toExpr(stmt, resultIndexing);
            resultExprs.addAll(subResult.exprs);
            resultIndexing = subResult.indexing;
        }

        return StmtUnfoldResult.of(resultExprs, resultIndexing);
    }

    ////////

    private static class StmtToExprVisitor implements StmtVisitor<VarIndexing, StmtUnfoldResult> {
        private static final StmtToExprVisitor INSTANCE = new StmtToExprVisitor();

        private StmtToExprVisitor() {
        }

        @Override
        public StmtUnfoldResult visit(final SkipStmt stmt, final VarIndexing indexing) {
            return StmtUnfoldResult.of(ImmutableList.of(True()), indexing);
        }

        @Override
        public StmtUnfoldResult visit(final AssumeStmt stmt, final VarIndexing indexing) {
            final Expr<BoolType> cond = stmt.getCond();
            final Expr<BoolType> expr = ExprUtils.applyPrimes(cond, indexing);
            return StmtUnfoldResult.of(ImmutableList.of(expr), indexing);
        }

        @Override
        public <DeclType extends Type> StmtUnfoldResult visit(final HavocStmt<DeclType> stmt,
                                                              final VarIndexing indexing) {
            final VarDecl<?> varDecl = stmt.getVarDecl();
            final VarIndexing newIndexing = indexing.inc(varDecl);
            return StmtUnfoldResult.of(ImmutableList.of(True()), newIndexing);
        }

        @Override
        public <DeclType extends Type> StmtUnfoldResult visit(final AssignStmt<DeclType> stmt,
                                                              final VarIndexing indexing) {
            final VarDecl<DeclType> varDecl = stmt.getVarDecl();
            final VarIndexing newIndexing = indexing.inc(varDecl);
            final Expr<DeclType> rhs = ExprUtils.applyPrimes(stmt.getExpr(), indexing);
            final Expr<DeclType> lhs = ExprUtils.applyPrimes(varDecl.getRef(), newIndexing);

            final Expr<BoolType> expr;
            if(varDecl.getType() instanceof FpType) {
                expr = FpAssign(TypeUtils.cast(lhs, (FpType)varDecl.getType()), TypeUtils.cast(rhs, (FpType)varDecl.getType()));
            } else {
                expr = Eq(lhs, rhs);
            }
            return StmtUnfoldResult.of(ImmutableList.of(expr), newIndexing);
        }

        @Override
        public StmtUnfoldResult visit(SequenceStmt sequenceStmt, VarIndexing indexing) {
            final StmtUnfoldResult result = toExpr(sequenceStmt.getStmts(), indexing);
            return StmtUnfoldResult.of(ImmutableList.of(And(result.getExprs())), result.getIndexing());
        }

        @Override
        public StmtUnfoldResult visit(NonDetStmt nonDetStmt, VarIndexing indexing) {

            final List<Expr<BoolType>> choices = new ArrayList<>();
            final List<VarIndexing> indexings = new ArrayList<>();
            VarIndexing jointIndexing = indexing;
            int count = 0;
            VarDecl<IntType> tempVar = VarPoolUtil.requestInt();
            for (Stmt stmt : nonDetStmt.getStmts()) {
                final Expr<BoolType> tempExpr = Eq(ExprUtils.applyPrimes(tempVar.getRef(), indexing), Int(count++));
                final StmtUnfoldResult result = toExpr(stmt, indexing.inc(tempVar));
                choices.add(And(tempExpr, And(result.exprs)));
                indexings.add(result.indexing);
                jointIndexing = jointIndexing.join(result.indexing);
            }
            final Set<VarDecl<?>> vars = ExprUtils.getVars(choices);
            final List<Expr<BoolType>> branchExprs = new ArrayList<>();
            for (int i = 0; i < choices.size(); i++) {
                final List<Expr<BoolType>> exprs = new ArrayList<>();
                exprs.add(choices.get(i));
                for (VarDecl<?> decl : vars) {
                    int currentBranchIndex = indexings.get(i).get(decl);
                    int jointIndex = jointIndexing.get(decl);
                    if (currentBranchIndex < jointIndex) {
                        if (currentBranchIndex > 0)
                            exprs.add(Eq(Prime(decl.getRef(), currentBranchIndex), Prime(decl.getRef(), jointIndex)));
                        else exprs.add(Eq(decl.getRef(), Prime(decl.getRef(), jointIndex)));
                    }
                }
                branchExprs.add(And(exprs));
            }
            final Expr<BoolType> expr = Or(branchExprs);
            VarPoolUtil.returnInt(tempVar);
            return StmtUnfoldResult.of(ImmutableList.of(expr), jointIndexing);
        }

		@Override
		public <DeclType extends Type> StmtUnfoldResult visit(PushStmt<DeclType> stmt, VarIndexing param) {
			if(param instanceof PushPopVarIndexing) {
				final PushPopVarIndexing newIndexing = ((PushPopVarIndexing) param).push(stmt.getVarDecl());
				return StmtUnfoldResult.of(ImmutableList.of(True()), newIndexing);
			}
//			return StmtUnfoldResult.of(ImmutableList.of(True()), param);
			throw new UnsupportedOperationException();
		}

		@Override
		public <DeclType extends Type> StmtUnfoldResult visit(PopStmt<DeclType> stmt, VarIndexing param) {
			if(param instanceof PushPopVarIndexing) {
				final PushPopVarIndexing newIndexing = ((PushPopVarIndexing) param).pop(stmt.getVarDecl());
				return StmtUnfoldResult.of(ImmutableList.of(True()), newIndexing);
			}
//			return StmtUnfoldResult.of(ImmutableList.of(True()), param);
			throw new UnsupportedOperationException();
		}

        @Override
        public StmtUnfoldResult visit(IfStmt ifStmt, VarIndexing indexing) {
            final Expr<BoolType> cond = ifStmt.getCond();
            final Expr<BoolType> condExpr = ExprUtils.applyPrimes(cond, indexing);

            final StmtUnfoldResult thenResult = toExpr(ifStmt.getThen(), indexing.transform().build());
            final StmtUnfoldResult elzeResult = toExpr(ifStmt.getElze(), indexing.transform().build());

            final VarIndexing thenIndexing = thenResult.indexing;
            final VarIndexing elzeIndexing = elzeResult.indexing;

            final Expr<BoolType> thenExpr = And(thenResult.getExprs());
            final Expr<BoolType> elzeExpr = And(elzeResult.getExprs());
            final Set<VarDecl<?>> vars = ExprUtils.getVars(ImmutableList.of(thenExpr, elzeExpr));

            VarIndexing jointIndexing = thenIndexing.join(elzeIndexing);
            final List<Expr<BoolType>> thenAdditions = new ArrayList<>();
            final List<Expr<BoolType>> elzeAdditions = new ArrayList<>();
            for (VarDecl<?> decl : vars) {
                final int thenIndex = thenIndexing.get(decl);
                final int elzeIndex = elzeIndexing.get(decl);
                if (thenIndex < elzeIndex) {
                    if (thenIndex > 0) {
                        thenAdditions.add(Eq(Prime(decl.getRef(), thenIndex), Prime(decl.getRef(), elzeIndex)));
                    } else {
                        thenAdditions.add(Eq(decl.getRef(), Prime(decl.getRef(), elzeIndex)));
                    }
                } else if (elzeIndex < thenIndex) {
                    if (elzeIndex > 0) {
                        elzeAdditions.add(Eq(Prime(decl.getRef(), elzeIndex), Prime(decl.getRef(), thenIndex)));
                    } else {
                        elzeAdditions.add(Eq(decl.getRef(), Prime(decl.getRef(), thenIndex)));
                    }
                }
            }

            final Expr<BoolType> thenExprExtended = thenAdditions.size() > 0 ? SmartBoolExprs.And(thenExpr, And(thenAdditions)) : thenExpr;
            final Expr<BoolType> elzeExprExtended = elzeAdditions.size() > 0 ? SmartBoolExprs.And(elzeExpr, And(elzeAdditions)) : elzeExpr;

            final Expr<BoolType> ite = cast(Ite(condExpr, thenExprExtended, elzeExprExtended), Bool());
            return StmtUnfoldResult.of(ImmutableList.of(ite), jointIndexing);
        }

        @Override
        public StmtUnfoldResult visit(OrtStmt ortStmt, VarIndexing indexing) {
            throw new UnsupportedOperationException();
        }

        @Override
        public StmtUnfoldResult visit(LoopStmt stmt, VarIndexing indexing) {
            throw new UnsupportedOperationException(String.format("Loop statement %s was not unrolled", stmt));
        }
    }
}
