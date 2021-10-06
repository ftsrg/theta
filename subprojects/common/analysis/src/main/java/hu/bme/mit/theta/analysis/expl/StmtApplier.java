/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.expl;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public final class StmtApplier {
    public enum ApplyResult {
        FAILURE, SUCCESS, BOTTOM
    }

    private StmtApplier() {
    }

    public static ApplyResult apply(final Stmt stmt, final MutableValuation val, final boolean approximate) {
        if (stmt instanceof AssignStmt) {
            final AssignStmt<?> assignStmt = (AssignStmt<?>) stmt;
            return applyAssign(assignStmt, val, approximate);
        } else if (stmt instanceof AssumeStmt) {
            final AssumeStmt assumeStmt = (AssumeStmt) stmt;
            return applyAssume(assumeStmt, val, approximate);
        } else if (stmt instanceof HavocStmt) {
            final HavocStmt<?> havocStmt = (HavocStmt<?>) stmt;
            return applyHavoc(havocStmt, val);
        } else if (stmt instanceof SkipStmt) {
            return applySkip();
        } else if (stmt instanceof SequenceStmt) {
            final SequenceStmt sequenceStmt = (SequenceStmt) stmt;
            return applySequence(sequenceStmt, val, approximate);
        } else if (stmt instanceof NonDetStmt) {
            final NonDetStmt nonDetStmt = (NonDetStmt) stmt;
            return applyNonDet(nonDetStmt, val, approximate);
        } else if (stmt instanceof OrtStmt) {
            final OrtStmt ortStmt = (OrtStmt) stmt;
            return applyOrt(ortStmt, val, approximate);
        } else if (stmt instanceof LoopStmt) {
            final LoopStmt loopStmt = (LoopStmt) stmt;
            return applyLoop(loopStmt, val, approximate);
        } else if (stmt instanceof IfStmt) {
            final IfStmt ifStmt = (IfStmt) stmt;
            return applyIf(ifStmt, val, approximate);
        } else {
            throw new UnsupportedOperationException("Unhandled statement: " + stmt);
        }
    }

    private static ApplyResult applyAssign(final AssignStmt<?> stmt, final MutableValuation val,
                                           final boolean approximate) {
        final VarDecl<?> varDecl = stmt.getVarDecl();
        final Expr<?> expr = ExprUtils.simplify(stmt.getExpr(), val);
        if (expr instanceof LitExpr<?>) {
            final LitExpr<?> lit = (LitExpr<?>) expr;
            val.put(varDecl, lit);
            return ApplyResult.SUCCESS;
        } else if (approximate) {
            val.remove(varDecl);
            return ApplyResult.SUCCESS;
        } else {
            return ApplyResult.FAILURE;
        }
    }

    private static ApplyResult applyAssume(final AssumeStmt stmt, final MutableValuation val,
                                           final boolean approximate) {
        final Expr<BoolType> cond = ExprUtils.simplify(stmt.getCond(), val);
        if (cond instanceof BoolLitExpr) {
            final BoolLitExpr condLit = (BoolLitExpr) cond;
            if (condLit.getValue()) {
                return ApplyResult.SUCCESS;
            } else {
                return ApplyResult.BOTTOM;
            }
        } else if (checkAssumeVarEqualsLit(cond, val)) {
            return ApplyResult.SUCCESS;
        } else {
            if (approximate) {
                return ApplyResult.SUCCESS;
            } else {
                return ApplyResult.FAILURE;
            }
        }
    }

    // Helper function to evaluate assumptions of form [x = 1] or [not x != 1]
    private static boolean checkAssumeVarEqualsLit(final Expr<BoolType> cond, final MutableValuation val) {
        RefExpr<?> ref = null;
        LitExpr<?> lit = null;

        if (cond instanceof EqExpr<?>) {
            final EqExpr<?> condEq = (EqExpr<?>) cond;

            if (condEq.getLeftOp() instanceof RefExpr<?> && condEq.getRightOp() instanceof LitExpr<?>) {
                ref = (RefExpr<?>) condEq.getLeftOp();
                lit = (LitExpr<?>) condEq.getRightOp();
            }

            if (condEq.getRightOp() instanceof RefExpr<?> && condEq.getLeftOp() instanceof LitExpr<?>) {
                ref = (RefExpr<?>) condEq.getRightOp();
                lit = (LitExpr<?>) condEq.getLeftOp();
            }
        }

        if (cond instanceof NotExpr) {
            final NotExpr condNE = (NotExpr) cond;
            if (condNE.getOp() instanceof NeqExpr<?>) {
                final NeqExpr<?> condNeq = (NeqExpr<?>) condNE.getOp();

                if (condNeq.getLeftOp() instanceof RefExpr<?> && condNeq.getRightOp() instanceof LitExpr<?>) {
                    ref = (RefExpr<?>) condNeq.getLeftOp();
                    lit = (LitExpr<?>) condNeq.getRightOp();
                }

                if (condNeq.getRightOp() instanceof RefExpr<?> && condNeq.getLeftOp() instanceof LitExpr<?>) {
                    ref = (RefExpr<?>) condNeq.getRightOp();
                    lit = (LitExpr<?>) condNeq.getLeftOp();
                }
            }
        }

        if (ref != null && lit != null) {
            val.put(ref.getDecl(), lit);
            return true;
        }

        return false;
    }

    private static ApplyResult applyHavoc(final HavocStmt<?> stmt, final MutableValuation val) {
        final VarDecl<?> varDecl = stmt.getVarDecl();
        val.remove(varDecl);
        return ApplyResult.SUCCESS;
    }

    private static ApplyResult applySkip() {
        return ApplyResult.SUCCESS;
    }

    private static ApplyResult applySequence(final SequenceStmt stmt, final MutableValuation val,
                                             final boolean approximate) {
        MutableValuation copy = MutableValuation.copyOf(val);
        for (Stmt subStmt : stmt.getStmts()) {
            ApplyResult res = apply(subStmt, copy, approximate);
            if (res == ApplyResult.BOTTOM || res == ApplyResult.FAILURE) return res;
        }
        val.clear();
        val.putAll(copy);
        return ApplyResult.SUCCESS;
    }

    private static ApplyResult applyLoop(final LoopStmt stmt, final MutableValuation val,
                                         final boolean approximate) {
        throw new UnsupportedOperationException(String.format("Loop statement %s was not unrolled", stmt));
    }

    private static ApplyResult applyNonDet(final NonDetStmt stmt, final MutableValuation val,
                                           final boolean approximate) {
        List<MutableValuation> valuations = new ArrayList<MutableValuation>();
        int successIndex = -1;
        for (int i = 0; i < stmt.getStmts().size(); i++) {
            MutableValuation subVal = MutableValuation.copyOf(val);
            ApplyResult res = apply(stmt.getStmts().get(i), subVal, approximate);
            if (res == ApplyResult.FAILURE) return ApplyResult.FAILURE;
            if (res == ApplyResult.SUCCESS) {
                valuations.add(subVal);
                if (successIndex == -1) successIndex = i;
            }
        }
        if (valuations.size() == 0) {
            return ApplyResult.BOTTOM;
        } else if (valuations.size() == 1) {
            return apply(stmt.getStmts().get(successIndex), val, approximate);
        } else if (approximate) {
            apply(stmt.getStmts().get(successIndex), val, approximate);
            List<Decl<?>> toRemove = new ArrayList<Decl<?>>();
            for (Decl<?> decl : val.getDecls()) {
                for (MutableValuation subVal : valuations) {
                    if (!val.eval(decl).equals(subVal.eval(decl))) {
                        toRemove.add(decl);
                        break;
                    }
                }
            }
            for (Decl<?> decl : toRemove) val.remove(decl);
            return ApplyResult.SUCCESS;
        } else {
            return ApplyResult.FAILURE;
        }
    }

    private static ApplyResult applyIf(final IfStmt stmt, final MutableValuation val,
                                       final boolean approximate) {
        final Expr<BoolType> cond = ExprUtils.simplify(stmt.getCond(), val);

        if (cond instanceof BoolLitExpr) {
            final BoolLitExpr condLit = (BoolLitExpr) cond;
            if (condLit.getValue()) {
                return apply(stmt.getThen(), val, approximate);
            } else {
                return apply(stmt.getElze(), val, approximate);
            }
        } else {
            final MutableValuation thenVal = MutableValuation.copyOf(val);
            final MutableValuation elzeVal = MutableValuation.copyOf(val);

            final ApplyResult thenResult = apply(stmt.getThen(), thenVal, approximate);
            final ApplyResult elzeResult = apply(stmt.getElze(), elzeVal, approximate);

            if (thenResult == ApplyResult.FAILURE || elzeResult == ApplyResult.FAILURE) {
                return ApplyResult.FAILURE;
            }

            if (thenResult == ApplyResult.BOTTOM && elzeResult == ApplyResult.BOTTOM) {
                return ApplyResult.BOTTOM;
            }

            if (thenResult == ApplyResult.SUCCESS && elzeResult == ApplyResult.BOTTOM) {
                SequenceStmt seq = SequenceStmt.of(ImmutableList.of(AssumeStmt.of(cond), stmt.getThen()));
                return apply(seq, val, approximate);
            }

            if (thenResult == ApplyResult.BOTTOM && elzeResult == ApplyResult.SUCCESS) {
                SequenceStmt seq = SequenceStmt.of(ImmutableList.of(AssumeStmt.of(Not(cond)), stmt.getElze()));
                return apply(seq, val, approximate);
            }

            if (approximate) {
                apply(stmt.getThen(), val, approximate);
                var toRemove = val.getDecls().stream()
                        .filter(it -> !val.eval(it).equals(elzeVal.eval(it)))
                        .collect(Collectors.toSet());
                for (Decl<?> decl : toRemove) val.remove(decl);
                return ApplyResult.SUCCESS;
            } else {
                return ApplyResult.FAILURE;
            }
        }
    }

    private static ApplyResult applyOrt(final OrtStmt stmt, final MutableValuation val,
                                        final boolean approximate) {
        throw new UnsupportedOperationException();
    }


	private static ApplyResult applyPush(final PushStmt<?> stmt, final MutableValuation val) {
		final VarDecl<?> varDecl = stmt.getVarDecl();
		val.remove(varDecl);
		return ApplyResult.SUCCESS;
	}


	private static ApplyResult applyPop(final PopStmt<?> stmt, final MutableValuation val) {
		final VarDecl<?> varDecl = stmt.getVarDecl();
		val.remove(varDecl);
		return ApplyResult.SUCCESS;
	}

}
