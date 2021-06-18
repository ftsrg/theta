package hu.bme.mit.theta.xsts.analysis.maxatomcount;

import hu.bme.mit.theta.analysis.expr.refinement.maxatomcount.IndividualMaxAtomCount;
import hu.bme.mit.theta.analysis.expr.refinement.maxatomcount.MaxAtomCount;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.AtomCollector;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class XstsAllExprsMaxAtomCountFactory implements XstsMaxAtomCountFactory {
    @Override
    public MaxAtomCount create(XSTS xsts) {
        final Set<Expr<BoolType>> atoms = Containers.createSet();
        atoms.addAll(AtomCollector.collectAtoms(xsts.getEnv()));
        atoms.addAll(AtomCollector.collectAtoms(xsts.getInit()));
        atoms.addAll(AtomCollector.collectAtoms(xsts.getTran()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getInitFormula()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getProp()));

        final Set<Expr<BoolType>> canonicalAtoms = atoms.stream()
                .map(ExprUtils::canonize)
                .collect(Collectors.toSet());
        final Map<VarDecl<?>,Set<Expr<BoolType>>> declToAtoms = Containers.createMap();
        canonicalAtoms.forEach(
                atom -> ExprUtils.getVars(atom).forEach(
                        decl -> declToAtoms.computeIfAbsent(decl,(k) -> Containers.createSet()).add(atom)
                )
        );

        final Map<VarDecl<?>, Integer> atomCount = Containers.createMap();
        xsts.getVars().forEach(
                decl -> atomCount.put(decl, declToAtoms.computeIfAbsent(decl,(k) -> Containers.createSet()).size())
        );
        return new IndividualMaxAtomCount(atomCount);
    }
}
