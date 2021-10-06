package hu.bme.mit.theta.xcfa.analysis.common.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.NewAtomsAutoExpl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.utils.XcfaUtils;

import java.util.Set;
import java.util.stream.Collectors;

public class XcfaNewAtomsAutoExpl implements XcfaAutoExpl {
    @Override
    public AutoExpl create(XCFA xcfa) {
        final Set<Expr<BoolType>> atoms = XcfaUtils.getAtoms(xcfa);

        final Set<Expr<BoolType>> canonicalAtoms = atoms.stream()
                .map(ExprUtils::canonize)
                .flatMap(atom -> ExprUtils.getAtoms(atom).stream())
                .collect(Collectors.toSet());
        return new NewAtomsAutoExpl(Set.of(),canonicalAtoms,0);
    }
}
