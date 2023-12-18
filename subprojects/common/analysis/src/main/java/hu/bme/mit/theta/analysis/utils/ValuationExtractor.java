package hu.bme.mit.theta.analysis.utils;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;

import java.util.Collection;

public interface ValuationExtractor <S extends State> {

    Valuation extractValuation(final S state);

    Valuation extractValuationForVars(final S state, final Collection<VarDecl<?>> vars);
}
