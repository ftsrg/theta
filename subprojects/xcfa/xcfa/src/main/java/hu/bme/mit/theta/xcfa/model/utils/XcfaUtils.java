/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.*;

import java.util.*;

public class XcfaUtils {

	private static final HashMap<XcfaProcedure, List<XcfaLocation>> atomicBlockInnerLocationsCache = new HashMap<>();

	/**
	 * Returns XCFA locations that are inner locations of any atomic block (after an edge with an AtomicBegin and before
	 * an edge with an AtomicEnd).
	 *
	 * @param xcfaProcedure the atomic block inner locations of this XCFA procedure will be returned
	 * @return the list of locations in an atomic block
	 */
	public static List<XcfaLocation> getAtomicBlockInnerLocations(XcfaProcedure xcfaProcedure) {
		if (atomicBlockInnerLocationsCache.containsKey(xcfaProcedure)) {
			return atomicBlockInnerLocationsCache.get(xcfaProcedure);
		}
		List<XcfaLocation> atomicBlockInnerLocations = getAtomicBlockInnerLocations(xcfaProcedure.getInitLoc());
		atomicBlockInnerLocationsCache.put(xcfaProcedure, atomicBlockInnerLocations);
		return atomicBlockInnerLocations;
	}

	/**
	 * Returns XCFA locations that are inner locations of any atomic block (after an edge with an AtomicBegin and before
	 * an edge with an AtomicEnd).
	 *
	 * @param builder the atomic block inner locations of the procedure of this builder will be returned
	 * @return the list of locations in an atomic block
	 */
	public static List<XcfaLocation> getAtomicBlockInnerLocations(XcfaProcedure.Builder builder) {
		return getAtomicBlockInnerLocations(builder.getInitLoc());
	}

	private static List<XcfaLocation> getAtomicBlockInnerLocations(XcfaLocation initialLocation) {
		List<XcfaLocation> atomicLocations = new ArrayList<>();
		List<XcfaLocation> visitedLocations = new ArrayList<>();
		List<XcfaLocation> locationsToVisit = new ArrayList<>();
		HashMap<XcfaLocation, Boolean> isAtomic = new HashMap<>();
		locationsToVisit.add(initialLocation);
		isAtomic.put(initialLocation, false);

		while (!locationsToVisit.isEmpty()) {
			XcfaLocation visiting = locationsToVisit.remove(0);
			if (isAtomic.get(visiting)) atomicLocations.add(visiting);
			visitedLocations.add(visiting);

			for (XcfaEdge outEdge : visiting.getOutgoingEdges()) {
				boolean isNextAtomic = isAtomic.get(visiting);
				if (outEdge.getLabels().stream().anyMatch(label -> label instanceof XcfaLabel.AtomicBeginXcfaLabel)) {
					isNextAtomic = true;
				}
				if (outEdge.getLabels().stream().anyMatch(label -> label instanceof XcfaLabel.AtomicEndXcfaLabel)) {
					isNextAtomic = false;
				}

				XcfaLocation target = outEdge.getTarget();
				isAtomic.put(target, isNextAtomic);
				if (atomicLocations.contains(target) && !isNextAtomic) {
					atomicLocations.remove(target);
				}
				if (!locationsToVisit.contains(target) && !visitedLocations.contains(target)) {
					locationsToVisit.add(outEdge.getTarget());
				}
			}
		}
		return atomicLocations;
	}

	public static Collection<VarDecl<?>> getVars(XCFA xcfa) {
		Set<VarDecl<?>> ret = new LinkedHashSet<>(xcfa.getGlobalVars());
		xcfa.getProcesses().forEach(process -> {
			ret.addAll(process.getParams());
			ret.addAll(process.getThreadLocalVars());
			process.getProcedures().forEach(procedure -> {
				ret.addAll(procedure.getParams().keySet());
				ret.addAll(procedure.getLocalVars());
			});
		});
		return ret;
	}

	public static Set<Expr<BoolType>> getAtoms(XCFA xcfa) {
		Set<Expr<BoolType>> atoms = new LinkedHashSet<>();
		xcfa.getProcesses().forEach(process -> {
			process.getProcedures().forEach(procedure -> {
				procedure.getEdges().forEach(xcfaEdge -> {
					xcfaEdge.getLabels().forEach(label -> {
						label.accept(XcfaAtomCollecter.INSTANCE, atoms);
					});
				});
			});
		});
		return atoms;
	}
}
