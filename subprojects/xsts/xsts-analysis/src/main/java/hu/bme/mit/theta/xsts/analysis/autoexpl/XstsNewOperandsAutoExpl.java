package hu.bme.mit.theta.xsts.analysis.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.NewOperandsAutoExpl;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtAtomCollector;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class XstsNewOperandsAutoExpl implements XstsAutoExpl {
    @Override
    public AutoExpl create(XSTS xsts) {
        final Set<Expr<BoolType>> atoms = Containers.createSet();
        atoms.addAll(StmtAtomCollector.collectAtoms(xsts.getEnv()));
        atoms.addAll(StmtAtomCollector.collectAtoms(xsts.getInit()));
        atoms.addAll(StmtAtomCollector.collectAtoms(xsts.getTran()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getProp()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getInitFormula()));

        final Set<Expr<BoolType>> canonicalAtoms = atoms.stream()
                .map(ExprUtils::canonize)
                .flatMap(atom -> ExprUtils.getAtoms(atom).stream())
                .collect(Collectors.toSet());
        final Map<Decl<?>,Set<Expr<?>>> declToOps = Containers.createMap();
        canonicalAtoms.stream()
                .filter(atom -> atom.getOps().size() > 1)
                .forEach(
                        atom -> {
                            atom.getOps().stream()
                                    .filter(RefExpr.class::isInstance)
                                    .map(RefExpr.class::cast)
                                    .forEach(
                                            ref -> atom.getOps().stream()
                                                    .filter(Predicate.not(ref::equals))
                                                    .forEach(
                                                            op -> declToOps.computeIfAbsent(ref.getDecl(), k -> Containers.createSet()).add((op))
                                                    )
                                    );
                        }
                );
        return new NewOperandsAutoExpl(xsts.getCtrlVars(),declToOps,0);
    }
}
