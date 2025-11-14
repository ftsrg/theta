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

package hu.bme.mit.theta.solver.meta;

import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.*;

public class MetaItpPattern implements ItpPattern {

    private final Map<ItpSolver, ItpPattern> patternMap;

    public MetaItpPattern(Map<ItpSolver, ItpPattern> patternMap) {
        this.patternMap = new ConcurrentHashMap<>(patternMap);
    }

    @Override
    public <E> E visit(ItpPatternVisitor<E> visitor) {
        ExecutorService executorService = Executors.newFixedThreadPool(patternMap.size());
        List<Callable<E>> tasks = new ArrayList<>();

        for (ItpPattern pattern : patternMap.values()) {
            tasks.add( () -> pattern.visit( visitor ) );
        }

        E item;
        try {
            item = executorService.invokeAny(tasks);
        } catch (InterruptedException | ExecutionException e) {
            throw new MetaSolverException(e);
        }
        executorService.shutdown();
        return item;
    }

    public ItpPattern getPattern(ItpSolver solver) {
        return patternMap.get(solver);
    }

    public void remove(ItpSolver solver) {
        patternMap.remove(solver);
    }
}
