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
package hu.bme.mit.theta.frontend.petrinet.analysis;

import hu.bme.mit.theta.common.table.TableWriter;
import java.util.Arrays;

public final class ModelProperties {
    private static final String[] headers =
            new String[] {
                "id",
                "Name",
                "Type",
                "#Place",
                "#Transition",
                "#Arc",
                "HasReadOnlyEffect",
                "HasReadOnlyEffectOnTop"
            };

    private final PtNetSystem model;
    private final String id;

    public ModelProperties(final PtNetSystem model, String id) {
        this.model = model;
        this.id = id;
    }

    public static void printHeader(TableWriter writer) {
        writer.cells(Arrays.asList(headers));
        writer.newRow();
    }

    public void printData(TableWriter writer) {
        writer.cell(id);
        writer.cell(model.getName());
        writer.cell("P/T net");
        writer.cell(model.getPlaceCount());
        writer.cell(model.getTransitionCount());
        writer.cell(model.getArcCount());
        writer.cell(model.hasReadOnlyEffect);
        writer.cell(model.hasReadOnlyEffectOnTop);
        writer.newRow();
    }
}
