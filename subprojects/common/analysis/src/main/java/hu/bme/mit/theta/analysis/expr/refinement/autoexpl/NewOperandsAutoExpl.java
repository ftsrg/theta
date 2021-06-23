package hu.bme.mit.theta.analysis.expr.refinement.autoexpl;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class NewOperandsAutoExpl implements AutoExpl{

    private final Set<VarDecl<?>> explVars = Containers.createSet();
    private final Map<Decl<?>,Set<Expr<?>>> modelOperands;
    private final Map<Decl<?>,Set<Expr<?>>> newOperands;
    private final int newOperandsLimit;

    public NewOperandsAutoExpl(final Set<VarDecl<?>> explPreferredVars, final Map<Decl<?>,Set<Expr<?>>> modelOperands, final int newOperandsLimit){
        explVars.addAll(explPreferredVars);
        this.newOperandsLimit = newOperandsLimit;
        this.modelOperands = modelOperands;

        this.newOperands = Containers.createMap();
    }

    @Override
    public boolean isExpl(VarDecl<?> decl) {
        return explVars.contains(decl);
    }

    @Override
    public void update(Expr<BoolType> itp) {

        final Set<Expr<BoolType>> canonicalAtoms = ExprUtils.getAtoms(itp).stream()
                .map(ExprUtils::canonize)
                .flatMap(atom -> ExprUtils.getAtoms(atom).stream())
                .collect(Collectors.toSet());
        canonicalAtoms.stream()
                .filter(BinaryExpr.class::isInstance)
                .map(BinaryExpr.class::cast)
                .forEach(
                        atom -> {
                            if(atom.getLeftOp() instanceof RefExpr) {
                                final Decl<?> decl = ((RefExpr<?>) atom.getLeftOp()).getDecl();
                                if(modelOperands.containsKey(decl) && !modelOperands.get(decl).contains(atom.getRightOp())) newOperands.computeIfAbsent(decl, k -> Containers.createSet()).add(atom.getRightOp());
                            }
                            if(atom.getRightOp() instanceof RefExpr) {
                                final Decl<?> decl = ((RefExpr<?>) atom.getRightOp()).getDecl();
                                if(modelOperands.containsKey(decl) && !modelOperands.get(decl).contains(atom.getLeftOp())) newOperands.computeIfAbsent(decl, k -> Containers.createSet()).add(atom.getLeftOp());
                            }
                        }
                );

        explVars.addAll(
                ExprUtils.getVars(itp).stream()
                        .filter(decl -> newOperands.containsKey(decl) && newOperands.get(decl).size() > newOperandsLimit || decl.getType() == Bool())
                        .collect(Collectors.toSet()));

    }
}
