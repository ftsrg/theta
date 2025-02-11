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
package hu.bme.mit.theta.frontend.petrinet.model.utils;

import hu.bme.mit.theta.frontend.petrinet.model.*;

public final class GraphVizSerializer {
    public static String toDot(PetriNet pn) {
        StringBuilder sb = new StringBuilder();
        sb.append("digraph PN {\n");

        for (Place p : pn.getPlaces()) {
            sb.append(
                    "\""
                            + p.getId()
                            + "\" [label=\""
                            + p.getId()
                            + (p.getInitialMarking() != 0
                                    ? "\\n(" + p.getInitialMarking() + ")"
                                    : "")
                            + "\"];\n");
        }
        for (Transition t : pn.getTransitions()) {
            sb.append("\"" + t.getId() + "\" [shape=box,label=\"" + t.getId() + "\"];\n");
        }
        for (PTArc pt : pn.getPtArcs()) {
            sb.append(
                    "\""
                            + pt.getSource().getId()
                            + "\" -> \""
                            + pt.getTarget().getId()
                            + "\" [label=\""
                            + (pt.getWeight() != 1 ? pt.getWeight() : "")
                            + "\"");

            if (pt.isInhibitor()) {
                sb.append(",arrowhead=dot");
            }

            sb.append("];\n");
        }
        for (TPArc tp : pn.getTpArcs()) {
            sb.append(
                    "\""
                            + tp.getSource().getId()
                            + "\" -> \""
                            + tp.getTarget().getId()
                            + "\" [label=\""
                            + (tp.getWeight() != 1 ? tp.getWeight() : "")
                            + "\"];\n");
        }

        sb.append("}\n");

        return sb.toString();
    }
}
