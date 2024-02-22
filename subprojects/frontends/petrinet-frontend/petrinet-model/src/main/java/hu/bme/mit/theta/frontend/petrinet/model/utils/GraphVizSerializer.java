package hu.bme.mit.theta.frontend.petrinet.model.utils;

import hu.bme.mit.theta.frontend.petrinet.model.*;

public final class GraphVizSerializer {
    public static String toDot(PetriNet pn) {
        StringBuilder sb = new StringBuilder();
        sb.append("digraph PN {\n");

        for (Place p : pn.getPlaces()) {
            sb.append("\"" +
                    p.getId() +
                    "\" [label=\"" +
                    p.getId() +
                    (p.getInitialMarking() != 0 ? "\\n(" + p.getInitialMarking() + ")" : "") +
                    "\"];\n");
        }
        for (Transition t : pn.getTransitions()) {
            sb.append("\"" + t.getId() + "\" [shape=box,label=\"" + t.getId() + "\"];\n");
        }
        for (PTArc pt : pn.getPtArcs()) {
            sb.append("\"" + pt.getSource().getId() + "\" -> \"" + pt.getTarget().getId() + "\" [label=\"" + (pt.getWeight() != 1 ? pt.getWeight() : "") + "\"");

            if (pt.isInhibitor()) {
                sb.append(",arrowhead=dot");
            }

            sb.append("];\n");
        }
        for (TPArc tp : pn.getTpArcs()) {
            sb.append("\"" + tp.getSource().getId() + "\" -> \"" + tp.getTarget().getId() + "\" [label=\"" + (tp.getWeight() != 1 ? tp.getWeight() : "") + "\"];\n");
        }

        sb.append("}\n");

        return sb.toString();
    }
}
