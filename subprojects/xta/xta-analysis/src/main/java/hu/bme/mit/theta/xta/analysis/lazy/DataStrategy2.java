/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xta.analysis.lazy;

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

    private static final Collection<DataStrategy2> VALID_DATA_STRATEGIES = List.of(
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
