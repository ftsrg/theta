package hu.bme.mit.theta.frontend.mdd;

import com.koloboke.collect.map.hash.HashObjObjMaps;
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
	public static List<Place> fromFile(String orderingPath, PetriNet petriNet) throws Exception {
		final File orderingFile = new File(orderingPath);
		if (!orderingFile.exists()) {
			throw new IOException("Cannot open ordering file: " + orderingPath);
		}
		List<String> orderingIds = Files.readAllLines(orderingFile.toPath());
		orderingIds.removeIf(s -> s.trim().isEmpty());
		if (orderingIds.size() != petriNet.getPlaces().size()) {
			throw new Exception("The ordering does not match the net: different number of entries");
		}
		Map<String, Place> placeIdMap = HashObjObjMaps.newImmutableMap(petriNet
			.getPlaces()
			.stream()
			.collect(Collectors.toMap(p -> p.getId(), p -> p)));
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
