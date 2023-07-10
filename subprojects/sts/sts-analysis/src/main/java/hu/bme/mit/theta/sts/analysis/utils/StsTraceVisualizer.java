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
package hu.bme.mit.theta.sts.analysis.utils;

import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.sts.analysis.StsAction;

public final class StsTraceVisualizer {

    private StsTraceVisualizer() {
    }

    public static void printTraceTable(final Trace<Valuation, StsAction> trace,
                                       final TableWriter writer) {
        final Set<Decl<?>> allVars = new LinkedHashSet<>();
        for (final Valuation val : trace.getStates()) {
            allVars.addAll(val.getDecls());
        }

        writer.startTable();
        allVars.forEach(v -> writer.cell(v.getName()));
        writer.newRow();
        for (final Valuation val : trace.getStates()) {
            for (final Decl<?> decl : allVars) {
                final Optional<?> eval = val.eval(decl);
                final String evalStr = eval.isPresent() ? eval.get().toString() : "";
                writer.cell(evalStr);
            }
            writer.newRow();
        }
        writer.endTable();
    }

}
