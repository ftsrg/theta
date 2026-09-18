/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.frontend.transformation.model.declaration;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Registry of the integer ids used to model a function's address. A function pointer variable holds
 * one of these ids, and a call through it is dispatched over the set of functions whose address was
 * taken (the "candidate set").
 *
 * <p>Ids start well above the data-pointer range (which the malloc/reference machinery allocates
 * from zero upwards) so that a function id can never be confused with the base address of a data
 * object, and are never zero so that a function pointer is distinguishable from NULL.
 *
 * <p>Entries accumulate per process, like the struct/enum registries; each input file is parsed in
 * its own process, and re-parsing the same file simply re-registers the same names.
 */
public final class FunctionIds {

    /** Well above any data-object base address, and never zero (which models NULL). */
    private static final int FIRST_ID = 0x10000000;

    private static final Map<String, Integer> ids = new LinkedHashMap<>();

    private static boolean indirectCallPresent = false;

    private FunctionIds() {}

    /**
     * Records that the program calls through a function pointer. Function ids are only ever
     * dispatched on by such a call, so a program without one needs no id variables at all and is
     * left completely unchanged (a function's address may also be taken merely to hand it to
     * pthread_create, which resolves it by name).
     */
    public static void markIndirectCall() {
        indirectCallPresent = true;
    }

    public static boolean hasIndirectCall() {
        return indirectCallPresent;
    }

    /** The id of a function whose address is taken, assigning one on first use. */
    public static int idOf(String functionName) {
        return ids.computeIfAbsent(functionName, name -> FIRST_ID + ids.size());
    }

    /** The id already assigned to this function, or {@code null} if its address is never taken. */
    public static Integer getId(String functionName) {
        return ids.get(functionName);
    }

    /** The functions whose address was taken, i.e. the candidate set for indirect calls. */
    public static Map<String, Integer> getAll() {
        return Collections.unmodifiableMap(ids);
    }
}
