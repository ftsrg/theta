/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.multi.builder;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.multi.*;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.unit.UnitState;

@SuppressWarnings("java:S119")
public class MultiBuilderResultPOJO<
        LState extends State,
        RState extends State,
        DataState extends State,
        LBlank extends State,
        RBlank extends State,
        LAction extends Action,
        RAction extends Action,
        LPrec extends Prec,
        RPrec extends Prec,
        DataPrec extends Prec,
        LBlankPrec extends Prec,
        RBlankPrec extends Prec,
        MState extends MultiState<LBlank, RBlank, DataState>,
        MBlankState extends MultiState<LBlank, RBlank, UnitState>,
        MAction extends MultiAction<LAction, RAction>,
        MLts extends
                MultiLts<
                                LState,
                                RState,
                                DataState,
                                LBlank,
                                RBlank,
                                LAction,
                                RAction,
                                MState,
                                MAction>> {
    private final MultiAnalysisSide<
                    MState,
                    DataState,
                    MBlankState,
                    MAction,
                    MultiPrec<LPrec, RPrec, DataPrec>,
                    MultiPrec<LBlankPrec, RBlankPrec, UnitPrec>>
            side;
    private final MLts lts;

    public MultiBuilderResultPOJO(
            MultiAnalysisSide<
                            MState,
                            DataState,
                            MBlankState,
                            MAction,
                            MultiPrec<LPrec, RPrec, DataPrec>,
                            MultiPrec<LBlankPrec, RBlankPrec, UnitPrec>>
                    side,
            MLts lts) {
        this.side = side;
        this.lts = lts;
    }

    public MultiAnalysisSide<
                    MState,
                    DataState,
                    MBlankState,
                    MAction,
                    MultiPrec<LPrec, RPrec, DataPrec>,
                    MultiPrec<LBlankPrec, RBlankPrec, UnitPrec>>
            getSide() {
        return side;
    }

    public MLts getLts() {
        return lts;
    }
}
