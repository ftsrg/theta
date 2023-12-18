package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.utils.ValuationExtractor;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;

import java.util.Collection;
import java.util.Map;

public final class ExplStateValuationExtractor implements ValuationExtractor<ExplState> {

    private static final class LazyHolder {
        private static final ExplStateValuationExtractor INSTANCE = new ExplStateValuationExtractor();
    }

    private ExplStateValuationExtractor() {
    }

    public static ExplStateValuationExtractor getInstance() {
        return ExplStateValuationExtractor.LazyHolder.INSTANCE;
    }

    @Override
    public Valuation extractValuation(ExplState state) {
        return state.getVal();
    }

    @Override
    public Valuation extractValuationForVars(ExplState state, Collection<VarDecl<?>> vars) {

        final ImmutableValuation.Builder builder = ImmutableValuation.builder();

        final Map<Decl<?>, LitExpr<?>> varToValue = state.getVal().toMap();

        for (final VarDecl<?> varDecl : vars) {
            final LitExpr<?> value = varToValue.get(varDecl);
            if (value != null) {
                builder.put(varDecl, value);
            }
        }

        return builder.build();
    }
}
