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
package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

import java.util.Collection;
import java.util.Map;

public class MultiprocInitFunc<S extends State, P extends Prec> {
    private final Map<Integer, InitFunc<S, P>> initFuncMap;

    public MultiprocInitFunc(final Map<Integer, InitFunc<S, P>> initFuncMap) {
        this.initFuncMap = initFuncMap;
    }

    public Collection<? extends S> getInitStates(final int pid, final P prec) {
        if (initFuncMap.containsKey(pid)) return initFuncMap.get(pid).getInitStates(prec);
        else
            throw new RuntimeException("No such process: " + pid + ". Known processes: " + initFuncMap.keySet());
    }

}
