package hu.bme.mit.theta.xsts.analysis.timed;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.*;
import hu.bme.mit.theta.core.type.clocktype.ClockConstraintExpr;
import hu.bme.mit.theta.core.type.clocktype.ClockExprs;
import hu.bme.mit.theta.core.type.clocktype.ClockType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.*;

import java.util.*;

import static hu.bme.mit.theta.core.stmt.Stmts.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static java.util.stream.Collectors.toList;

public class ControlFlowSplitUtil {

    private ControlFlowSplitUtil() {
    }

    public static ControlFlowSplitResult splitControlFlows(final Stmt stmt) {

        final List<VarDecl<BoolType>> flags = new ArrayList<>();
        final List<Expr<BoolType>> controlFlowConstraints = new ArrayList<>();

        final ControlFlowEncodingHelper helper = new ControlFlowEncodingHelper(flags, controlFlowConstraints);
        final Stmt flaggedStmt = helper.encodeControlFlows(stmt);

        for (final VarDecl<BoolType> flag : Lists.reverse(flags)) {
            VarPoolUtil.returnBool(flag);
        }

        return ControlFlowSplitResult.of(flaggedStmt, flags, controlFlowConstraints);
    }

    private static final class ControlFlowEncodingHelper implements StmtVisitor<VarDecl<BoolType>, Stmt> {

        private final List<VarDecl<BoolType>> flags;
        private final List<Expr<BoolType>> controlFlowConstraints;
        private final AssumeTransformationHelper assumeHelper;

        private ControlFlowEncodingHelper(final List<VarDecl<BoolType>> flags,
                                          final List<Expr<BoolType>> controlFlowConstraints) {
            this.flags = flags;
            this.controlFlowConstraints = controlFlowConstraints;
            assumeHelper = new AssumeTransformationHelper();
        }

        public Stmt encodeControlFlows(final Stmt stmt) {
            final VarDecl<BoolType> root = VarPoolUtil.requestBool();
            flags.add(root);
            controlFlowConstraints.add(root.getRef());

            final Stmt transformedStmt = stmt.accept(this, root);
            final AssumeStmt controlFlowAssumptions = Stmts.Assume(And(controlFlowConstraints));

            return Stmts.SequenceStmt(List.of(transformedStmt, controlFlowAssumptions));
        }

        @Override
        public Stmt visit(SkipStmt stmt, VarDecl<BoolType> parent) {
            return stmt;
        }

        @Override
        public Stmt visit(AssumeStmt stmt, VarDecl<BoolType> parent) {
            if (!stmt.accept(StmtContainsTimingVisitor.getInstance(), null)) {
                return stmt;
            }
            return assumeHelper.transformAssume(stmt.getCond(), parent);
        }

        @Override
        public <DeclType extends Type> Stmt visit(AssignStmt<DeclType> stmt, VarDecl<BoolType> parent) {
            final VarDecl<DeclType> varDecl = stmt.getVarDecl();

            if (!(varDecl.getType() instanceof BoolType) || !stmt.accept(StmtContainsTimingVisitor.getInstance(), null)) {
                return stmt;
            }

            final Expr<DeclType> assignExpr = stmt.getExpr();
            final Expr<BoolType> cond = TypeUtils.cast(assignExpr, Bool());
            final VarDecl<BoolType> boolVarDecl = TypeUtils.cast(varDecl, Bool());
            final AssignStmt<BoolType> then = Assign(boolVarDecl, True());
            final AssignStmt<BoolType> elze = Assign(boolVarDecl, False());

            final IfStmt assignToIfStmt = IfStmt(cond, then, elze);
            return assignToIfStmt.accept(this, parent);
        }

        @Override
        public <DeclType extends Type> Stmt visit(HavocStmt<DeclType> stmt, VarDecl<BoolType> parent) {
            return stmt;
        }

        @Override
        public Stmt visit(SequenceStmt stmt, VarDecl<BoolType> parent) {
            final List<Stmt> transformedSubStmts = stmt.getStmts().stream()
                    .map(subStmt -> subStmt.accept(this, parent))
                    .toList();
            return SequenceStmt(transformedSubStmts);
        }

        @Override
        public Stmt visit(NonDetStmt stmt, VarDecl<BoolType> parent) {
            if (!stmt.accept(StmtContainsTimingVisitor.getInstance(), null)) {
                return stmt;
            }

            final List<Stmt> branches = stmt.getStmts();
            final int branchCnt = branches.size();

            if (branchCnt == 1) {
                return branches.get(0).accept(this, parent);
            }

            final List<VarDecl<BoolType>> localFlags = new ArrayList<>(branchCnt);
            final List<Stmt> transformedBranches = new ArrayList<>(branchCnt);

            for (final Stmt branch : branches) {
                final VarDecl<BoolType> flag = VarPoolUtil.requestBool();
                localFlags.add(flag);
                flags.add(flag);
                controlFlowConstraints.add(Imply(Not(parent.getRef()), Not(flag.getRef())));

                final Stmt transformedBranchBody = branch.accept(this, flag);
                final IfStmt transformedBranch = IfStmt(flag.getRef(), transformedBranchBody);
                transformedBranches.add(transformedBranch);
            }

            final List<Expr<BoolType>> branchExprs = new ArrayList<>();
            for (int i = 0; i < localFlags.size(); i++) {
                final List<Expr<BoolType>> flagsForCurrentBranch = new ArrayList<>();
                for (int j = 0; j < localFlags.size(); j++) {
                    final RefExpr<BoolType> flagExpr = localFlags.get(j).getRef();
                    flagsForCurrentBranch.add((i == j) ? flagExpr : Not(flagExpr));
                }
                branchExprs.add(And(flagsForCurrentBranch));
            }
            controlFlowConstraints.add(Imply(parent.getRef(), Or(branchExprs)));

            return SequenceStmt(transformedBranches);
        }

        @Override
        public Stmt visit(OrtStmt stmt, VarDecl<BoolType> parent) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Stmt visit(LoopStmt stmt, VarDecl<BoolType> parent) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Stmt visit(IfStmt stmt, VarDecl<BoolType> parent) {
            if (!stmt.accept(StmtContainsTimingVisitor.getInstance(), null)) {
                return stmt;
            }

            final Map<Expr<BoolType>, Stmt> condToBranch = new LinkedHashMap<>(2, 1);
            condToBranch.put(stmt.getCond(), stmt.getThen());
            condToBranch.put(Not(stmt.getCond()), stmt.getElze());

            final List<VarDecl<BoolType>> localFlags = new ArrayList<>(2);
            final List<Stmt> transformedBranches = new ArrayList<>(2);

            for (final Map.Entry<Expr<BoolType>, Stmt> branch : condToBranch.entrySet()) {
                final VarDecl<BoolType> flag = VarPoolUtil.requestBool();
                localFlags.add(flag);
                flags.add(flag);

                final Expr<BoolType> cond = branch.getKey();
                final Stmt branchBody = branch.getValue();
                final Stmt newBranchBody = SequenceStmt(List.of(Assume(cond), branchBody));
                final Stmt transformedBranchBody = newBranchBody.accept(this, flag);

                final IfStmt transformedBranch = IfStmt(flag.getRef(), transformedBranchBody);
                transformedBranches.add(transformedBranch);
            }

            final Expr<BoolType> p = parent.getRef();
            final Expr<BoolType> b1 = localFlags.get(0).getRef();
            final Expr<BoolType> b2 = localFlags.get(1).getRef();
            controlFlowConstraints.add(Imply(p, Xor(b1, b2)));
            controlFlowConstraints.add(Imply(Not(p), Not(b1)));
            controlFlowConstraints.add(Imply(Not(p), Not(b2)));

            return SequenceStmt(transformedBranches);
        }

        @Override
        public Stmt visit(DelayStmt stmt, VarDecl<BoolType> parent) {
            return stmt;
        }

        @Override
        public Stmt visit(ResetStmt stmt, VarDecl<BoolType> parent) {
            return stmt;
        }


        private final class AssumeTransformationHelper {

            private AssumeTransformationHelper() {
            }

            private Stmt transformAssume(final Expr<BoolType> cond, final VarDecl<BoolType> parent) {
                if (cond instanceof NotExpr) {
                    return transformNot((NotExpr) cond, parent);
                } else if (cond instanceof AndExpr) {
                    return transformAnd((AndExpr) cond, parent);
                } else if (cond instanceof OrExpr) {
                    return transformOr((OrExpr) cond, parent);
                } else if (cond instanceof ImplyExpr) {
                    return transformImply((ImplyExpr) cond, parent);
                } else if (cond instanceof IffExpr) {
                    return transformIff((IffExpr) cond, parent);
                } else if (cond instanceof XorExpr) {
                    return transformXor((XorExpr) cond, parent);
                } else if (cond instanceof QuantifiedExpr) {
                    throw new UnsupportedOperationException();
                } else {
                    return Assume(cond);
                }
            }

            private Stmt transformAnd(final AndExpr andExpr, final VarDecl<BoolType> parent) {
                final List<Stmt> assumes = andExpr.getOps().stream().map(Stmts::Assume).collect(toList());
                final Stmt transformed = SequenceStmt(assumes);
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformOr(final OrExpr orExpr, final VarDecl<BoolType> parent) {
                final List<Stmt> assumes = orExpr.getOps().stream().map(Stmts::Assume).collect(toList());
                final Stmt transformed = NonDetStmt(assumes);
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformImply(final ImplyExpr implyExpr, final VarDecl<BoolType> parent) {
                final Expr<BoolType> a = implyExpr.getLeftOp();
                final Expr<BoolType> b = implyExpr.getRightOp();
                final Stmt transformed = Assume(Or(Not(a), b));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformIff(final IffExpr iffExpr, final VarDecl<BoolType> parent) {
                final Expr<BoolType> a = iffExpr.getLeftOp();
                final Expr<BoolType> b = iffExpr.getRightOp();
                final Expr<BoolType> imply1 = Or(Not(a), b);
                final Expr<BoolType> imply2 = Or(Not(b), a);
                final Stmt transformed = Assume(And(imply1, imply2));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformXor(final XorExpr xorExpr, final VarDecl<BoolType> parent) {
                final Expr<BoolType> a = xorExpr.getLeftOp();
                final Expr<BoolType> b = xorExpr.getRightOp();
                final Expr<BoolType> case1 = And(Not(a), b);
                final Expr<BoolType> case2 = And(a, Not(b));
                final Stmt transformed = Assume(Or(case1, case2));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformNot(final NotExpr notExpr, final VarDecl<BoolType> parent) {
                final Expr<BoolType> op = notExpr.getOp();
                if (op instanceof ClockConstraintExpr) {
                    return transformNegatedClockConstraint((ClockConstraintExpr) op);
                } else if (op instanceof NotExpr) {
                    return transformNegatedNot((NotExpr) op, parent);
                } else if (op instanceof AndExpr) {
                    return transformNegatedAnd((AndExpr) op, parent);
                } else if (op instanceof OrExpr) {
                    return transformNegatedOr((OrExpr) op, parent);
                } else if (op instanceof ImplyExpr) {
                    return transformNegatedImply((ImplyExpr) op, parent);
                } else if (op instanceof IffExpr) {
                    return transformNegatedIff((IffExpr) op, parent);
                } else if (op instanceof XorExpr) {
                    return transformNegatedXor((XorExpr) op, parent);
                } else if (op instanceof ExistsExpr) {
                    return transformNegatedExists((ExistsExpr) op, parent);
                } else if (op instanceof ForallExpr) {
                    return transformNegatedForall((ForallExpr) op, parent);
                } else {
                    return Assume(notExpr);
                }
            }

            private Stmt transformNegatedClockConstraint(final ClockConstraintExpr negatedClockConstraint) {
                final Expr<ClockType> clock = negatedClockConstraint.getLeftOp();
                final Expr<IntType> value = negatedClockConstraint.getRightOp();
                final ClockConstraintExpr complement = switch (negatedClockConstraint.getRel()) {
                    case LT -> ClockExprs.Geq(clock, value);
                    case LEQ -> ClockExprs.Gt(clock, value);
                    case GT -> ClockExprs.Leq(clock, value);
                    case GEQ -> ClockExprs.Lt(clock, value);
                    default -> throw new UnsupportedOperationException();
                };
                return Assume(complement);
            }

            private Stmt transformNegatedNot(final NotExpr negatedNotExpr, final VarDecl<BoolType> parent) {
                final Stmt transformed = Assume(negatedNotExpr.getOp());
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformNegatedAnd(final AndExpr negatedAndExpr, final VarDecl<BoolType> parent) {
                final List<NotExpr> negatedOps = negatedAndExpr.getOps().stream().map(BoolExprs::Not).toList();
                final Stmt transformed = Assume(Or(negatedOps));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformNegatedOr(final OrExpr negatedOrExpr, final VarDecl<BoolType> parent) {
                final List<NotExpr> negatedOps = negatedOrExpr.getOps().stream().map(BoolExprs::Not).toList();
                final Stmt transformed = Assume(And(negatedOps));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformNegatedImply(final ImplyExpr negatedImplyExpr, final VarDecl<BoolType> parent) {
                final Expr<BoolType> a = negatedImplyExpr.getLeftOp();
                final Expr<BoolType> b = negatedImplyExpr.getRightOp();
                final Stmt transformed = Assume(And(a, Not(b)));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformNegatedIff(final IffExpr negatedIffExpr, final VarDecl<BoolType> parent) {
                final Expr<BoolType> a = negatedIffExpr.getLeftOp();
                final Expr<BoolType> b = negatedIffExpr.getRightOp();
                final Expr<BoolType> notImply1 = And(a, Not(b));
                final Expr<BoolType> notImply2 = And(b, Not(a));
                final Stmt transformed = Assume(Or(notImply1, notImply2));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformNegatedXor(final XorExpr negatedXorExpr, final VarDecl<BoolType> parent) {
                final Expr<BoolType> a = negatedXorExpr.getLeftOp();
                final Expr<BoolType> b = negatedXorExpr.getRightOp();
                final Expr<BoolType> same1 = And(a, b);
                final Expr<BoolType> same2 = And(Not(a), Not(b));
                final Stmt transformed = Assume(Or(same1, same2));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformNegatedExists(final ExistsExpr negatedExistsExpr, final VarDecl<BoolType> parent) {
                final List<ParamDecl<?>> params = negatedExistsExpr.getParamDecls();
                final Expr<BoolType> op = negatedExistsExpr.getOp();
                final Stmt transformed = Assume(Forall(params, Not(op)));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }

            private Stmt transformNegatedForall(final ForallExpr negatedForallExpr, final VarDecl<BoolType> parent) {
                final List<ParamDecl<?>> params = negatedForallExpr.getParamDecls();
                final Expr<BoolType> op = negatedForallExpr.getOp();
                final Stmt transformed = Assume(Exists(params, Not(op)));
                return transformed.accept(ControlFlowEncodingHelper.this, parent);
            }
        }
    }
}
