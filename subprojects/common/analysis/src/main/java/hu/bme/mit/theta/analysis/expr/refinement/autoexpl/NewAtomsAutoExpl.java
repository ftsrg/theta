package hu.bme.mit.theta.analysis.expr.refinement.autoexpl;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class NewAtomsAutoExpl implements AutoExpl{

    private final Set<VarDecl<?>> explVars = Containers.createSet();
    private final Set<Expr<BoolType>> modelAtoms;
    private final Map<VarDecl<?>,Set<Expr<BoolType>>> newAtoms;
    private final int newAtomsLimit;

    public NewAtomsAutoExpl(final Set<VarDecl<?>> explPreferredVars, final Set<Expr<BoolType>> modelAtoms, final int newAtomsLimit){
        explVars.addAll(explPreferredVars);
        this.modelAtoms = modelAtoms;
        this.newAtomsLimit = newAtomsLimit;

        this.newAtoms = Containers.createMap();
    }

    @Override
    public boolean isExpl(final VarDecl<?> decl) {
        return explVars.contains(decl);
    }

    @Override
    public void update(final Expr<BoolType> itp) {

        final var canonicalAtoms = ExprUtils.getAtoms(itp).stream()
                .map(ExprUtils::canonize)
                .flatMap(atom -> ExprUtils.getAtoms(atom).stream())
                .collect(Collectors.toSet());
        canonicalAtoms.stream()
                .filter(Predicate.not(modelAtoms::contains))
                .forEach(
                        atom -> ExprUtils.getVars(atom).forEach(
                                decl -> newAtoms.computeIfAbsent(decl,(k) -> Containers.createSet()).add(atom)
                        )
                );

         explVars.addAll(
                ExprUtils.getVars(itp).stream()
                        .filter(decl -> newAtoms.containsKey(decl) && newAtoms.get(decl).size() > newAtomsLimit || decl.getType() == Bool())
                        .collect(Collectors.toSet()));

    }
}
