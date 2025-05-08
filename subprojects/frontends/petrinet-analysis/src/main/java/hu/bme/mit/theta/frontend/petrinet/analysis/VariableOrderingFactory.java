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

import com.koloboke.collect.map.hash.HashObjObjMaps;
import hu.bme.mit.theta.frontend.petrinet.model.Identified;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public final class VariableOrderingFactory {
    public static List<Place> fromPathString(String orderingPath, PetriNet petriNet)
            throws Exception {
        final File orderingFile = new File(orderingPath);
        if (!orderingFile.exists()) {
            throw new IOException("Cannot open ordering file: " + orderingPath);
        }
        return fromFile(orderingFile, petriNet);
    }

    public static List<Place> fromFile(File orderingFile, PetriNet petriNet) throws Exception {
        List<String> orderingIds = Files.readAllLines(orderingFile.toPath());
        orderingIds.removeIf(s -> s.trim().isEmpty());
        if (orderingIds.size() != petriNet.getPlaces().size()) {
            throw new Exception("The ordering does not match the net: different number of entries");
        }
        Map<String, Place> placeIdMap =
                HashObjObjMaps.newImmutableMap(
                        petriNet.getPlaces().stream()
                                .collect(Collectors.toMap(Identified::getId, p -> p)));
        final List<Place> ordering = new ArrayList<>(orderingIds.size());
        for (String s : orderingIds) {
            Place p = placeIdMap.get(s);
            if (p == null) {
                throw new Exception("The ordering does not match the net: no place for ID " + s);
            }
            ordering.add(p);
        }
        return ordering;
    }
}
