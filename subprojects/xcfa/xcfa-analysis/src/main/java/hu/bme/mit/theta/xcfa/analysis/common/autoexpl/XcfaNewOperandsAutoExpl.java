package hu.bme.mit.theta.xcfa.analysis.common.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.NewOperandsAutoExpl;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.utils.XcfaUtils;

import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class XcfaNewOperandsAutoExpl implements XcfaAutoExpl {
    @Override
    public AutoExpl create(XCFA xcfa) {
        final Set<Expr<BoolType>> atoms = XcfaUtils.getAtoms(xcfa);

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
        return new NewOperandsAutoExpl(Set.copyOf(xcfa.getGlobalVars()),declToOps,0);
    }
}
