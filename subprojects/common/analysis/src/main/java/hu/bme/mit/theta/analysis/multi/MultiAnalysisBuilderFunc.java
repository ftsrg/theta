/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.multi;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

import java.util.function.Function;

@FunctionalInterface
public interface MultiAnalysisBuilderFunc<LState extends State, RState extends State, DataState extends State, LBlank extends State, RBlank extends State,
        LAction extends Action, RAction extends Action,
        LPrec extends Prec, RPrec extends Prec, DataPrec extends Prec, LBlankPrec extends Prec, RBlankPrec extends Prec,
        MState extends MultiState<LBlank, RBlank, DataState>, MAction extends MultiAction<LAction, RAction>,
        MAnalysis extends MultiAnalysis<LState, RState, DataState, LBlank, RBlank, LAction, RAction, LPrec, RPrec, DataPrec, LBlankPrec, RBlankPrec, MState, MAction>> {

    MAnalysis build(MultiAnalysis.Side<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> leftSide,
                    MultiAnalysis.Side<RState, DataState, RBlank, RAction, RPrec, RBlankPrec> rightSide,
                    Function<MState, MultiSourceSide> defineNextSide,
                    InitFunc<DataState, DataPrec> dataInitFunc);

}
