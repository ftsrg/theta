package hu.bme.mit.theta.xsts.analysis.autoexpl;

import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.NewOperandsAutoExpl;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.AtomCollector;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class XstsNewOperandsAutoExpl implements XstsAutoExpl {
    @Override
    public AutoExpl create(XSTS xsts) {
        final Set<Expr<BoolType>> atoms = Containers.createSet();
        atoms.addAll(AtomCollector.collectAtoms(xsts.getEnv()));
        atoms.addAll(AtomCollector.collectAtoms(xsts.getInit()));
        atoms.addAll(AtomCollector.collectAtoms(xsts.getTran()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getProp()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getInitFormula()));

        final Set<Expr<BoolType>> canonicalAtoms = atoms.stream()
                .map(ExprUtils::canonize)
                .flatMap(atom -> ExprUtils.getAtoms(atom).stream())
                .collect(Collectors.toSet());
        final Map<Decl<?>,Set<Expr<?>>> declToOps = Containers.createMap();
        canonicalAtoms.stream()
                .filter(BinaryExpr.class::isInstance)
                .map(BinaryExpr.class::cast)
                .forEach(
                        atom -> {
                            if(atom.getLeftOp() instanceof RefExpr) declToOps.computeIfAbsent(((RefExpr<?>) atom.getLeftOp()).getDecl(), k -> Containers.createSet()).add((atom.getRightOp()));
                            if(atom.getRightOp() instanceof RefExpr) declToOps.computeIfAbsent(((RefExpr<?>) atom.getRightOp()).getDecl(), k -> Containers.createSet()).add((atom.getLeftOp()));
                        }
                );
        return new NewOperandsAutoExpl(xsts.getCtrlVars(),declToOps,0);
    }
}
