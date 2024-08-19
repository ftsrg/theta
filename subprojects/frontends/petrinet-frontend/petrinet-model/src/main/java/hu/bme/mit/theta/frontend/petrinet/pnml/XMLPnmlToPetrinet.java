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
package hu.bme.mit.theta.frontend.petrinet.pnml;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.frontend.petrinet.model.*;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.xpath.*;
import java.io.IOException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class XMLPnmlToPetrinet {

    private XMLPnmlToPetrinet() {
    }

    public static PetriNet parse(final String fileName, final String initialMarkingString)
            throws ParserConfigurationException, IOException, SAXException, XPathExpressionException {

        final DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        final DocumentBuilder builder = factory.newDocumentBuilder();
        final Document document = builder.parse(fileName);

        final Pattern pattern = Pattern.compile("([0-9]+\\s)*[0-9]+");
        final Matcher matcher = pattern.matcher(initialMarkingString);
        final boolean overrideInitialMarking = matcher.matches();
        final Integer[] values;
        if (overrideInitialMarking) {
            final String[] valueStrings = initialMarkingString.split("\\s");
            values = Arrays.stream(valueStrings).map(Integer::parseInt).toArray(Integer[]::new);
        } else {
            values = null;
        }

        final XPath xPath = XPathFactory.newInstance().newXPath();

        final Element pnmlElement = document.getDocumentElement();
        final NodeList netList = pnmlElement.getElementsByTagName("net");
        checkArgument(netList.getLength() == 1, "Pnml model contains multiple nets");
        final Element netElement = (Element) netList.item(0);

        final Map<String, Identified> idMap = Containers.createMap();
        final List<Place> places = new ArrayList<>();
        final List<Transition> transitions = new ArrayList<>();

        // Find all places
        final XPathExpression childPlacesExpr = xPath.compile("./place");
        final NodeList placeList = (NodeList) childPlacesExpr.evaluate(netElement,
                XPathConstants.NODESET);
        for (int i = 0; i < placeList.getLength(); i++) {
            final Element placeElement = (Element) placeList.item(i);
            final String id = placeElement.getAttribute("id");

//			final String name;
//			final XPathExpression nameTextExpr = xPath.compile("./name/text/text()");
//			final XPathExpression nameValueExpr = xPath.compile("./name/value/text()");
//			final String nameText = (String) nameTextExpr.evaluate(placeElement,XPathConstants.STRING);
//			if(nameText.equals("")){
//				name = (String) nameValueExpr.evaluate(placeElement,XPathConstants.STRING);
//			} else {
//				name = nameText;
//			}

            final int initialMarking;
            if (overrideInitialMarking) {
                initialMarking = values[i];
            } else {
                final XPathExpression initialMarkingTextExpr = xPath.compile(
                        "./initialMarking/text/text()");
                initialMarking = ((Double) initialMarkingTextExpr.evaluate(placeElement,
                        XPathConstants.NUMBER)).intValue();
            }

            final Place place = new Place(id);
            place.setInitialMarking(initialMarking);
            idMap.put(id, place);
            places.add(place);
        }

        // Find all transitions
        final XPathExpression childTransitionsExpr = xPath.compile("./transition");
        final NodeList transitionList = (NodeList) childTransitionsExpr.evaluate(netElement,
                XPathConstants.NODESET);
        for (int i = 0; i < transitionList.getLength(); i++) {
            final Element transitionElement = (Element) transitionList.item(i);
            final String id = transitionElement.getAttribute("id");

//			final String name;
//			final XPathExpression nameTextExpr = xPath.compile("./name/text/text()");
//			final XPathExpression nameValueExpr = xPath.compile("./name/value/text()");
//			final String nameText = (String) nameTextExpr.evaluate(transitionElement,XPathConstants.STRING);
//			if(nameText.equals("")){
//				name = (String) nameValueExpr.evaluate(transitionElement,XPathConstants.STRING);
//			} else {
//				name = nameText;
//			}

            final Transition transition = new Transition(id);
            idMap.put(id, transition);
            transitions.add(transition);
        }

        // Find all arcs
        final XPathExpression childArcsExpr = xPath.compile("./arc");
        final NodeList arcList = (NodeList) childArcsExpr.evaluate(netElement,
                XPathConstants.NODESET);
        for (int i = 0; i < arcList.getLength(); i++) {
            final Element arcElement = (Element) arcList.item(i);
            final String id = arcElement.getAttribute("id");

            final String sourceId = arcElement.getAttribute("source");
            final Identified source = idMap.get(sourceId);
            checkNotNull(source, "Source node not found of arc " + id);

            final String targetId = arcElement.getAttribute("target");
            final Identified target = idMap.get(targetId);
            checkNotNull(source, "Target node not found of arc " + id);

            final XPathExpression toolspecificWeightExpr = xPath.compile(
                    "./toolspecific/weight/text()");
            final int toolspecificWeight = ((Double) toolspecificWeightExpr.evaluate(arcElement,
                    XPathConstants.NUMBER)).intValue();
            final int weight = toolspecificWeight == 0 ? 1 : toolspecificWeight;

            if (source instanceof Place) {
                checkArgument(target instanceof Transition);
                final PTArc arc = new PTArc(id);
                arc.setWeight(weight);
                arc.setSource((Place) source);
                arc.setTarget((Transition) target);
            } else {
                checkArgument(source instanceof Transition && target instanceof Place);
                final TPArc arc = new TPArc(id);
                arc.setWeight(weight);
                arc.setSource((Transition) source);
                arc.setTarget((Place) target);
            }
        }

        final PetriNet ptNet = new PetriNet("0");
        ptNet.getPlaces().addAll(places);
        ptNet.getTransitions().addAll(transitions);

        return ptNet;
    }

}
