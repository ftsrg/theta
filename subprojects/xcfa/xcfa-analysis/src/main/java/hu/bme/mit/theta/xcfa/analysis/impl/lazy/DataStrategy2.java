package hu.bme.mit.theta.xcfa.analysis.impl.lazy;

import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public final class DataStrategy2 {

    public enum ConcrDom {
        EXPL, EXPR
    }
    public enum AbstrDom {
        NONE, EXPL, EXPR
    }
    public enum ItpStrategy {
        NONE, BIN_BW, BIN_FW, SEQ
    }

    private static final Collection<DataStrategy2> VALID_DATA_STRATEGIES = List.of (
            new DataStrategy2(ConcrDom.EXPL, AbstrDom.NONE, ItpStrategy.NONE),
            new DataStrategy2(ConcrDom.EXPL, AbstrDom.EXPL, ItpStrategy.BIN_BW),
            new DataStrategy2(ConcrDom.EXPL, AbstrDom.EXPL, ItpStrategy.BIN_FW),
            new DataStrategy2(ConcrDom.EXPL, AbstrDom.EXPR, ItpStrategy.BIN_BW),
            new DataStrategy2(ConcrDom.EXPL, AbstrDom.EXPR, ItpStrategy.BIN_FW),
            new DataStrategy2(ConcrDom.EXPL, AbstrDom.EXPR, ItpStrategy.SEQ),
            new DataStrategy2(ConcrDom.EXPR, AbstrDom.EXPR, ItpStrategy.SEQ)
    );

    private final ConcrDom concrDom;
    private final AbstrDom abstrDom;
    private final ItpStrategy itpStrategy;

    public DataStrategy2(final ConcrDom concrDom, final AbstrDom abstrDom, final ItpStrategy itpStrategy) {
        this.concrDom = checkNotNull(concrDom);
        this.abstrDom = checkNotNull(abstrDom);
        this.itpStrategy = checkNotNull(itpStrategy);
    }

    public ConcrDom getConcrDom() {
        return concrDom;
    }
    public AbstrDom getAbstrDom() {
        return abstrDom;
    }
    public ItpStrategy getItpStrategy() {
        return itpStrategy;
    }

    public static Collection<DataStrategy2> getValidStrategies() {
        return VALID_DATA_STRATEGIES;
    }

    public boolean isValid() {
        return VALID_DATA_STRATEGIES.contains(this);
    }

    @Override
    public String toString() {
        return "DataStrategy2{" +
                "concrDom=" + concrDom +
                ", abstrDom=" + abstrDom +
                ", itpStrategy=" + itpStrategy +
                '}';
    }
}
