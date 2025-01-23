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
package hu.bme.mit.theta.frontend.petrinet.pnml;

import fr.lip6.move.pnml.ptnet.*;
import fr.lip6.move.pnml.ptnet.hlapi.PetriNetDocHLAPI;
import hu.bme.mit.theta.frontend.petrinet.model.*;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.petrinet.model.Transition;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

final class Lip6PnmlToPetrinet {
    private final PetriNetDocHLAPI root;

    public Lip6PnmlToPetrinet(final PetriNetDocHLAPI root) {
        this.root = root;
    }

    public List<PetriNet> parse() throws PnmlParseException {
        fr.lip6.move.pnml.ptnet.PetriNetDoc pnDocDOM = root.getContainedItem();
        List<PetriNet> ret = new ArrayList<>();
        for (fr.lip6.move.pnml.ptnet.PetriNet pnDOM : pnDocDOM.getNets()) {
            PetriNet pn = new PetriNet(pnDOM.getId());
            if (pnDOM.getName() != null) {
                pn.setName(pnDOM.getName().getText());
            }
            // TODO parse NUPN

            List<fr.lip6.move.pnml.ptnet.Place> places = new ArrayList<>();
            List<fr.lip6.move.pnml.ptnet.Transition> transitions = new ArrayList<>();
            List<Arc> arcs = new ArrayList<>();
            for (Page pageDOM : pnDOM.getPages()) {
                for (PnObject object : pageDOM.getObjects()) {
                    if (object instanceof fr.lip6.move.pnml.ptnet.Place) {
                        places.add((fr.lip6.move.pnml.ptnet.Place) object);
                    } else if (object instanceof RefPlace) {
                        // refPlaces.add((RefPlace) object);
                    } else if (object instanceof fr.lip6.move.pnml.ptnet.Transition) {
                        transitions.add((fr.lip6.move.pnml.ptnet.Transition) object);
                    } else if (object instanceof RefTransition) {
                        // refTransitions.add((RefTransition) object);
                    } else if (object instanceof Arc) {
                        arcs.add((Arc) object);
                    } else {
                        throw new PnmlParseException("Unknown object: " + object);
                    }
                }
            }

            Map<String, Place> placeMap = new HashMap<>();
            Map<String, Transition> transitionMap = new HashMap<>();

            for (fr.lip6.move.pnml.ptnet.Place placeDOM : places) {
                Place p = new Place(placeDOM.getId());
                if (placeDOM.getInitialMarking() != null) {
                    p.setInitialMarking(placeDOM.getInitialMarking().getText());
                } else {
                    p.setInitialMarking(0);
                }

                placeMap.put(p.getId(), p);
                pn.getPlaces().add(p);
            }

            for (fr.lip6.move.pnml.ptnet.Transition transitionDOM : transitions) {
                Transition t = new Transition(transitionDOM.getId());

                transitionMap.put(t.getId(), t);
                pn.getTransitions().add(t);
            }

            for (Arc arcDOM : arcs) {
                if (arcDOM.getSource() instanceof fr.lip6.move.pnml.ptnet.PlaceNode) {
                    assert arcDOM.getTarget() instanceof fr.lip6.move.pnml.ptnet.TransitionNode;

                    PTArc arc = new PTArc(arcDOM.getId());
                    // TODO inhibitor??
                    String sourceId =
                            arcDOM.getSource() instanceof RefPlace
                                    ? ((RefPlace) arcDOM.getSource()).getRef().getId()
                                    : arcDOM.getSource().getId();
                    String targetId =
                            arcDOM.getTarget() instanceof RefTransition
                                    ? ((RefTransition) arcDOM.getTarget()).getRef().getId()
                                    : arcDOM.getTarget().getId();
                    Place sourcePlace = placeMap.get(sourceId);
                    Transition targetTransition = transitionMap.get(targetId);
                    arc.setSource(sourcePlace);
                    arc.setTarget(targetTransition);
                    if (arcDOM.getInscription() != null) {
                        arc.setWeight(arcDOM.getInscription().getText());
                    } else {
                        arc.setWeight(1);
                    }
                    pn.getPtArcs().add(arc);

                } else if (arcDOM.getSource() instanceof fr.lip6.move.pnml.ptnet.TransitionNode) {
                    assert arcDOM.getTarget() instanceof fr.lip6.move.pnml.ptnet.PlaceNode;

                    TPArc arc = new TPArc(arcDOM.getId());
                    // TODO inhibitor??
                    String sourceId =
                            arcDOM.getSource() instanceof RefTransition
                                    ? ((RefTransition) arcDOM.getSource()).getRef().getId()
                                    : arcDOM.getSource().getId();
                    String targetId =
                            arcDOM.getTarget() instanceof RefPlace
                                    ? ((RefPlace) arcDOM.getTarget()).getRef().getId()
                                    : arcDOM.getTarget().getId();
                    Transition sourceTransition = transitionMap.get(sourceId);
                    Place targetPlace = placeMap.get(targetId);
                    arc.setSource(sourceTransition);
                    arc.setTarget(targetPlace);
                    if (arcDOM.getInscription() != null) {
                        arc.setWeight(arcDOM.getInscription().getText());
                    } else {
                        arc.setWeight(1);
                    }
                    pn.getTpArcs().add(arc);
                }
            }
            ret.add(pn);
        }
        return ret;
    }
}
