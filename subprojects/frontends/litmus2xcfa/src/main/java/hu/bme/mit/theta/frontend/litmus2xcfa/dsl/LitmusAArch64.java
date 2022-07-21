/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.frontend.litmus2xcfa.dsl;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.litmus2xcfa.dsl.gen.LitmusAArch64BaseVisitor;
import hu.bme.mit.theta.litmus2xcfa.dsl.gen.LitmusAArch64Parser;
import hu.bme.mit.theta.xcfa.model.*;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;

import java.math.BigInteger;
import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.*;

public class LitmusAArch64 extends LitmusAArch64BaseVisitor<XCFA> {
    private final Map<String, Tuple2<VarDecl<BvType>, Optional<LitExpr<BvType>>>> vars;
    private final Map<Integer, Map<String, VarDecl<BvType>>> regLookup;
    private final List<Integer> threadIds;
    private final Map<Integer, Map<String, VarDecl<BvType>>> globalAddresses;
    private final Map<Integer, Map<String, XcfaLocation>> locations;
    private final Map<Integer, XcfaProcedure.Builder> builders;
    private final Map<Integer, XcfaLocation> lastLocation;
    private final LocationVisitor locationVisitor;
    private final ExpressionVisitor expressionVisitor;
    private final LabelVisitor labelVisitor;
    private int currentProc;

    public LitmusAArch64() {
        regLookup = new LinkedHashMap<>();
        labelVisitor = new LabelVisitor();
        expressionVisitor = new ExpressionVisitor();
        globalAddresses = new LinkedHashMap<>();
        lastLocation = new LinkedHashMap<>();
        locations = new LinkedHashMap<>();
        builders = new LinkedHashMap<>();
        vars = new LinkedHashMap<>();
        threadIds = new ArrayList<>();
        locationVisitor = new LocationVisitor();
    }

    @Override
    public XCFA visitMain(LitmusAArch64Parser.MainContext ctx) {
        XCFA.Builder builder = XCFA.builder();
        XcfaPassManager.clearXCFAPasses();
        XcfaPassManager.clearProcessPasses();
        XcfaPassManager.clearProcedurePasses();

        for (final LitmusAArch64Parser.VariableDeclaratorContext variableDeclaratorContext : ctx.variableDeclaratorList().variableDeclarator()) {
            final LitmusAArch64Parser.VariableDeclaratorLocationContext varDeclCtx = variableDeclaratorContext.variableDeclaratorLocation();
            final LitmusAArch64Parser.VariableDeclaratorRegisterLocationContext regDeclCtx = variableDeclaratorContext.variableDeclaratorRegisterLocation();
            if(varDeclCtx != null) {
                getGlobalFromName(varDeclCtx.location().getText(), BvUtils.bigIntegerToNeutralBvLitExpr(new BigInteger(varDeclCtx.constant().getText()), 64), builder);
            }
            else if(regDeclCtx != null && regDeclCtx.Amp() == null) {
                final int id = regDeclCtx.threadId().id;
                globalAddresses.putIfAbsent(id, new LinkedHashMap<>());
                globalAddresses.get(id).put(regDeclCtx.register64().getText(), getGlobalFromName(regDeclCtx.location().getText(), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 64), builder));
            } else {
                throw new UnsupportedOperationException("Only registers storing addresses of global variables are supported!");
            }
        }
        for (final LitmusAArch64Parser.ThreadIdContext threadIdContext : ctx.program().threadDeclaratorList().threadId()) {
            final int id = threadIdContext.id;
            regLookup.putIfAbsent(id, new LinkedHashMap<>());
            globalAddresses.putIfAbsent(id, new LinkedHashMap<>());
            locations.putIfAbsent(id, new LinkedHashMap<>());
            final XcfaProcess.Builder process = XcfaProcess.builder();
            final XcfaProcedure.Builder procedure = XcfaProcedure.builder();
            final XcfaLocation location = XcfaLocation.create("initial" + XcfaLocation.uniqueCounter());
            procedure.addLoc(location);
            process.addProcedure(procedure);
            process.setMainProcedure(procedure);
            builder.addProcess(process);
            procedure.setInitLoc(location);
            if(builder.getMainProcess() == null) builder.setMainProcess(process);
            builders.putIfAbsent(id, procedure);
            lastLocation.put(id, location);
            threadIds.add(id);
        }
        for (LitmusAArch64Parser.InstructionRowContext instructionRowContext : ctx.program().instructionList().instructionRow()) {
            List<LitmusAArch64Parser.InstructionContext> instruction = instructionRowContext.instruction();
            for (int i = 0; i < instruction.size(); i++) {
                final LitmusAArch64Parser.InstructionContext instructionContext = instruction.get(i);
                currentProc = threadIds.get(i);
                instructionContext.accept(locationVisitor);
            }
        }
        for (Integer threadId : threadIds) {
            builders.get(threadId).setFinalLoc(lastLocation.get(threadId));
        }
        return builder.build();
    }

    private VarDecl<BvType> getGlobalFromName(final String name, final LitExpr<BvType> litExpr, final XCFA.Builder builder) {
        if(!vars.containsKey(name)) {
            VarDecl<BvType> var = Var(name, BvType(64));
            builder.addvar(var, litExpr);
            vars.put(name, Tuple2.of(var, Optional.ofNullable(litExpr)));
        }
        return vars.get(name).get1();
    }

    private VarDecl<BvType> getOrCreateVar(final String name, final int size) {
        checkState(!globalAddresses.get(currentProc).containsKey(name), "Register cannot be modified if it holds an address!");
        if(!regLookup.get(currentProc).containsKey(name)) {
            final VarDecl<BvType> var = Var(name, BvType(size));
            regLookup.get(currentProc).put(name, var);
            builders.get(currentProc).createVar(var, null);
        }
        return regLookup.get(currentProc).get(name);
    }

    private VarDecl<BvType> getGlobalFromReg(final String name) {
        checkState(!regLookup.get(currentProc).containsKey(name), "Register cannot be modified if it holds an address!");
        checkState(globalAddresses.get(currentProc).containsKey(name), "Register holds an unknown address!");
        return globalAddresses.get(currentProc).get(name);
    }

    private XcfaLocation newAnonymousLoc() {
        return getOrCreateLoc("loc" + XcfaLocation.uniqueCounter());
    }

    private XcfaLocation getOrCreateLoc(final String name) {
        if(!locations.get(currentProc).containsKey(name)) {
            final XcfaLocation xcfaLocation = XcfaLocation.create(name);
            builders.get(currentProc).addLoc(xcfaLocation);
            locations.get(currentProc).put(name, xcfaLocation);
        }
        return locations.get(currentProc).get(name);
    }

    private class ExpressionVisitor extends LitmusAArch64BaseVisitor<Expr<BvType>> {
        @Override
        public Expr<BvType> visitExpressionConversion(LitmusAArch64Parser.ExpressionConversionContext ctx) {
            return ctx.register32().accept(this);
        }

        @Override
        public Expr<BvType> visitExpressionImmediate64(LitmusAArch64Parser.ExpressionImmediate64Context ctx) {
            return BvUtils.bigIntegerToNeutralBvLitExpr(new BigInteger(ctx.expressionImmediate().immediate().constant().getText()), 64);
        }

        @Override
        public Expr<BvType> visitExpressionImmediate32(LitmusAArch64Parser.ExpressionImmediate32Context ctx) {
            return BvUtils.bigIntegerToNeutralBvLitExpr(new BigInteger(ctx.expressionImmediate().immediate().constant().getText()), 32);
        }

        @Override
        public Expr<BvType> visitRegister64(LitmusAArch64Parser.Register64Context ctx) {
            return getOrCreateVar(ctx.getText(), 64).getRef();
        }

        @Override
        public Expr<BvType> visitRegister32(LitmusAArch64Parser.Register32Context ctx) {
            return getOrCreateVar(ctx.getText(), 32).getRef();
        }
    }

    private class LabelVisitor extends LitmusAArch64BaseVisitor<XcfaLabel> {
        @Override
        public XcfaLabel visitMov32(LitmusAArch64Parser.Mov32Context ctx) {
            return Stmt(Assign(getOrCreateVar(ctx.r32.getText(), 32), ctx.expr32().accept(expressionVisitor)));
        }

        @Override
        public XcfaLabel visitMov64(LitmusAArch64Parser.Mov64Context ctx) {
            return Stmt(Assign(getOrCreateVar(ctx.r64.getText(), 64), ctx.expr64().accept(expressionVisitor)));
        }

        @Override
        public XcfaLabel visitCmp32(LitmusAArch64Parser.Cmp32Context ctx) {
            return Stmt(Assign(getOrCreateVar("Xcmp", 32), Sub(ctx.r32.accept(expressionVisitor), ctx.expr32().accept(expressionVisitor))));
        }

        @Override
        public XcfaLabel visitCmp64(LitmusAArch64Parser.Cmp64Context ctx) {
            return Stmt(Assign(getOrCreateVar("Wcmp", 64), Sub(ctx.r64.accept(expressionVisitor), ctx.expr64().accept(expressionVisitor))));
        }

        @Override
        public XcfaLabel visitArith32(LitmusAArch64Parser.Arith32Context ctx) {
            final VarDecl<BvType> target = getOrCreateVar(ctx.rD32.getText(), 32);
            final Expr<BvType> a = ctx.rV32.accept(expressionVisitor);
            final Expr<BvType> b = ctx.expr32().accept(expressionVisitor);
            return switch (ctx.arithmeticInstruction().getText()) {
                case "ADD" -> Stmt(Assign(target, Add(List.of(a, b))));
                case "SUB" -> Stmt(Assign(target, Sub(a, b)));
                case "EOR" -> Stmt(Assign(target, Xor(List.of(a, b))));
                case "AND" -> Stmt(Assign(target, And(List.of(a, b))));
                default -> throw new UnsupportedOperationException("Arithmetic instruction " + ctx.arithmeticInstruction().getText() + " not supported.");
            };
        }

        @Override
        public XcfaLabel visitArith64(LitmusAArch64Parser.Arith64Context ctx) {
            final VarDecl<BvType> target = getOrCreateVar(ctx.rD64.getText(), 64);
            final Expr<BvType> a = ctx.rV64.accept(expressionVisitor);
            final Expr<BvType> b = ctx.expr64().accept(expressionVisitor);
            return switch (ctx.arithmeticInstruction().getText()) {
                case "ADD" -> Stmt(Assign(target, Add(List.of(a, b))));
                case "SUB" -> Stmt(Assign(target, Sub(a, b)));
                case "EOR" -> Stmt(Assign(target, Xor(List.of(a, b))));
                case "AND" -> Stmt(Assign(target, And(List.of(a, b))));
                default -> throw new UnsupportedOperationException("Arithmetic instruction " + ctx.arithmeticInstruction().getText() + " not supported.");
            };
        }

        @Override
        public XcfaLabel visitLoad32(LitmusAArch64Parser.Load32Context ctx) {
            final VarDecl<BvType> var = getOrCreateVar(ctx.rD32.getText(), 32);
            final VarDecl<BvType> tmp = getOrCreateVar("tmp" + XcfaLocation.uniqueCounter(), 64);
            StmtXcfaLabel cast = Stmt(Assign(var, Extract(tmp.getRef(), Int(0), Int(32))));
            LoadXcfaLabel<BvType> load = Load(getGlobalFromReg(ctx.address().r.getText()), tmp, true, ctx.loadInstruction().mo);
            return Sequence(List.of(load, cast));
        }

        @Override
        public XcfaLabel visitLoad64(LitmusAArch64Parser.Load64Context ctx) {
            return Load(getGlobalFromReg(ctx.address().r.getText()), getOrCreateVar(ctx.rD64.getText(), 32), true, ctx.loadInstruction().mo);
        }

        @Override
        public XcfaLabel visitStore32(LitmusAArch64Parser.Store32Context ctx) {
            final VarDecl<BvType> var = getOrCreateVar(ctx.rV32.getText(), 32);
            final VarDecl<BvType> tmp = getOrCreateVar("tmp" + XcfaLocation.uniqueCounter(), 64);
            StmtXcfaLabel cast = Stmt(Assign(tmp, ZExt(var.getRef(), BvType(64))));
            StoreXcfaLabel<BvType> store = Store(getGlobalFromReg(ctx.address().r.getText()), tmp, true, ctx.storeInstruction().mo);
            return Sequence(List.of(cast, store));
        }

        @Override
        public XcfaLabel visitStore64(LitmusAArch64Parser.Store64Context ctx) {
            return Store(getGlobalFromReg(ctx.address().r.getText()), getOrCreateVar(ctx.rV64.getText(), 64), true, ctx.storeInstruction().mo);
        }

        @Override
        public XcfaLabel visitFence(LitmusAArch64Parser.FenceContext ctx) {
            return Fence(ctx.Fence().getText() + (ctx.FenceOpt() == null ? "" : "." + ctx.FenceOpt().getText()));
        }
    }

    public class LocationVisitor extends LitmusAArch64BaseVisitor<XcfaLocation> {
        @Override
        public XcfaLocation visitBranchRegister32(LitmusAArch64Parser.BranchRegister32Context ctx) {
            VarDecl<BvType> var = getOrCreateVar(ctx.rV32.getText(), 32);
            final StmtXcfaLabel stmt1, stmt2;
            if(ctx.branchRegInstruction().zerotest) {
                stmt1 = Stmt(Assume(Eq(var.getRef(), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 32))));
                stmt2 = Stmt(Assume(Neq(var.getRef(), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 32))));
            } else {
                stmt1 = Stmt(Assume(Neq(var.getRef(), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 32))));
                stmt2 = Stmt(Assume(Eq(var.getRef(), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 32))));
            }
            final XcfaLocation branchTo = getOrCreateLoc(ctx.label().getText());
            final XcfaLocation newLoc = newAnonymousLoc();
            builders.get(currentProc).addEdge(XcfaEdge.of(
                    lastLocation.get(currentProc),
                    branchTo,
                    List.of(stmt1)));
            builders.get(currentProc).addEdge(XcfaEdge.of(
                    lastLocation.get(currentProc),
                    newLoc,
                    List.of(stmt2)));
            lastLocation.put(currentProc, newLoc);
            return newLoc;
        }
        @Override
        public XcfaLocation visitBranchRegister64(LitmusAArch64Parser.BranchRegister64Context ctx) {
            VarDecl<BvType> var = getOrCreateVar(ctx.rV64.getText(), 64);
            final StmtXcfaLabel stmt1, stmt2;
            if(ctx.branchRegInstruction().zerotest) {
                stmt1 = Stmt(Assume(Eq(var.getRef(), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 64))));
                stmt2 = Stmt(Assume(Neq(var.getRef(), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 64))));
            } else {
                stmt1 = Stmt(Assume(Neq(var.getRef(), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 64))));
                stmt2 = Stmt(Assume(Eq(var.getRef(), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 64))));
            }
            final XcfaLocation branchTo = getOrCreateLoc(ctx.label().getText());
            final XcfaLocation newLoc = newAnonymousLoc();
            builders.get(currentProc).addEdge(XcfaEdge.of(
                    lastLocation.get(currentProc),
                    branchTo,
                    List.of(stmt1)));
            builders.get(currentProc).addEdge(XcfaEdge.of(
                    lastLocation.get(currentProc),
                    newLoc,
                    List.of(stmt2)));
            lastLocation.put(currentProc, newLoc);
            return newLoc;
        }
        @Override
        public XcfaLocation visitBranch(LitmusAArch64Parser.BranchContext ctx) {
            final XcfaLocation branchTo = getOrCreateLoc(ctx.label().getText());
            final XcfaLocation newLoc = newAnonymousLoc();
            builders.get(currentProc).addEdge(XcfaEdge.of(
                    lastLocation.get(currentProc),
                    branchTo,
                    List.of()));
            lastLocation.put(currentProc, newLoc);
            return newLoc;
        }

        @Override
        public XcfaLocation visitBranchLabel(LitmusAArch64Parser.BranchLabelContext ctx) {
            final XcfaLocation newLoc = getOrCreateLoc(ctx.label().getText());
            builders.get(currentProc).addEdge(XcfaEdge.of(
                    lastLocation.get(currentProc),
                    newLoc,
                    List.of()));
            lastLocation.put(currentProc, newLoc);
            return newLoc;
        }

        @Override
        public XcfaLocation visitSimpleInstruction(LitmusAArch64Parser.SimpleInstructionContext ctx) {
            final XcfaLabel label = ctx.accept(labelVisitor);
            if(label != null) {
                final XcfaLocation newLoc = newAnonymousLoc();
                builders.get(currentProc).addEdge(XcfaEdge.of(
                        lastLocation.get(currentProc),
                        newLoc,
                        List.of(label)));
                lastLocation.put(currentProc, newLoc);
                return newLoc;
            }
            return lastLocation.get(currentProc);
        }

        @Override
        public XcfaLocation visitExclusiveInstruction(LitmusAArch64Parser.ExclusiveInstructionContext ctx) {
            throw new UnsupportedOperationException();
        }
    }
}
