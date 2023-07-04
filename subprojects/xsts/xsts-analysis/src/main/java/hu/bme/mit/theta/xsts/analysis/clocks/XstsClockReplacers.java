package hu.bme.mit.theta.xsts.analysis.clocks;

import hu.bme.mit.theta.core.clock.impl.*;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.Ordered;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.clocktype.ClockEqExpr;
import hu.bme.mit.theta.core.type.clocktype.ClockExprs;
import hu.bme.mit.theta.core.type.clocktype.ClockType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.type.XstsPrimitiveType;
import hu.bme.mit.theta.xsts.type.XstsType;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Stream;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.clocktype.ClockExprs.Clock;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class XstsClockReplacers {

    private XstsClockReplacers() {
    }

    public interface XstsClockReplacer extends Function<XSTS, XSTS> {
    }

    public static XstsClockReplacer None() {
        return xsts -> xsts;
    }

    public static XstsClockReplacer Int() {
        return xsts -> replaceClocks(xsts, IntClockImpl::fromClocks);
    }

    public static XstsClockReplacer Rat() {
        return xsts -> replaceClocks(xsts, RatClockImpl::fromClocks);
    }

    private static <T extends Ordered<T>> XSTS replaceClocks(
            final XSTS xsts,
            final Function<Collection<VarDecl<ClockType>>, ClockImpl<T>> clockImplFromClocks) {

        final Collection<VarDecl<ClockType>> clockVars = xsts.getVars().stream()
                .filter(v -> v.getType() instanceof ClockType)
                .map(v -> cast(v, Clock()))
                .toList();
        final ClockImpl<T> clockImpl = clockImplFromClocks.apply(clockVars);

        final Map<VarDecl<?>, XstsType<?>> varToType = xsts.getVarToType();
        for (VarDecl<ClockType> clockVar : clockVars) {
            varToType.remove(clockVar);
            final VarDecl<?> clockVarReplacement = clockImpl.transformVar(clockVar);
            varToType.put(clockVarReplacement, XstsPrimitiveType.of(clockVarReplacement.getType()));
        }

        final NonDetStmt init = (NonDetStmt) clockImpl.transformStmt(xsts.getInit());
        final NonDetStmt tran = (NonDetStmt) clockImpl.transformStmt(xsts.getTran());
        final NonDetStmt env = (NonDetStmt) clockImpl.transformStmt(xsts.getEnv());

        final Expr<BoolType> xstsInitFormula = xsts.getInitFormula();
        final Expr<BoolType> clockInitFormula = And(clockVars.stream().map(clock -> ClockExprs.Geq(clock.getRef(), IntExprs.Int(0))).toList());
        final Expr<BoolType> initFormula = clockImpl.transformExpr(And(xstsInitFormula, clockInitFormula));

        final Expr<BoolType> prop = clockImpl.transformExpr(xsts.getProp());

        return new XSTS(varToType, xsts.getCtrlVars(), init, tran, env, initFormula, prop);
    }
}
