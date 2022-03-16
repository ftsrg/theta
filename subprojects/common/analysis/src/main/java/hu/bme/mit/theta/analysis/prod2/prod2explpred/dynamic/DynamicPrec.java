package hu.bme.mit.theta.analysis.prod2.prod2explpred.dynamic;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.utils.ExprCanonizer;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Map;
import java.util.stream.Collectors;

public class DynamicPrec extends Prod2Prec<ExplPrec, PredPrec> {

    final Map<VarDecl<?>, Integer> predCounts;

    protected DynamicPrec(ExplPrec prec1, PredPrec prec2) {
        super(prec1, prec2);
        final var canonicalAtoms = prec2.getPreds().stream().flatMap(
                pred -> ExprUtils.getAtoms(pred).stream()
        ).map(ExprCanonizer::canonize).collect(Collectors.toSet());
        predCounts = Containers.createMap();
        canonicalAtoms.forEach(
                atom -> ExprUtils.getVars(atom).forEach(
                        decl -> predCounts.put(decl, predCounts.getOrDefault(decl, 0) + 1)
                )
        );
    }

    public Integer getPredCount(VarDecl<?> decl){
        return predCounts.getOrDefault(decl, 0);
    }

    public static DynamicPrec of(final ExplPrec prec1, final PredPrec prec2) {
        return new DynamicPrec(prec1, prec2);
    }
}
