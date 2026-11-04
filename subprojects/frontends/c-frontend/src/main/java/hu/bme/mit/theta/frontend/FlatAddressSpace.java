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
package hu.bme.mit.theta.frontend;

import static com.google.common.base.Preconditions.checkState;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.TreeMap;

/**
 * The compile-time half of the flat address line: every static object gets the slot `[start, start
 * + size + GAP)` right after the previous one, starting at {@link #FIRST} so that null (0) is no
 * object's address. Runtime objects continue from {@link #end()} (see `AllocationUtils` in xcfa).
 *
 * <p>The gap keeps one-past-the-end of an object out of its neighbour, and keeps zero-sized objects
 * at distinct addresses. Once {@link #end()} has been read the runtime counter is seeded from it,
 * so the space is sealed and any later static allocation is an error rather than a silent overlap.
 */
public final class FlatAddressSpace {

    public static final BigInteger FIRST = BigInteger.ONE;
    public static final BigInteger GAP = BigInteger.ONE;

    /** The slot reserved for an object whose extent the translation unit cannot know. */
    public static final BigInteger UNKNOWN_EXTENT = BigInteger.ONE.shiftLeft(16);

    /**
     * Slot [start, start + extent) of the object with raw id {@code id}; extent includes the gap.
     */
    public record Slot(BigInteger id, BigInteger start, BigInteger extent) {}

    private final Map<BigInteger, Slot> byId = new LinkedHashMap<>();
    private final TreeMap<BigInteger, Slot> byStart = new TreeMap<>();
    private BigInteger next = FIRST;
    private boolean sealed = false;

    /**
     * The start address of object {@code id}, allocating a slot of {@code size} units on first
     * request.
     */
    public BigInteger allocate(BigInteger id, BigInteger size) {
        final Slot existing = byId.get(id);
        if (existing != null) {
            return existing.start();
        }
        checkState(!sealed, "Static object allocated after the runtime counter was seeded");
        final Slot slot = new Slot(id, next, size.max(BigInteger.ZERO).add(GAP));
        byId.put(id, slot);
        byStart.put(slot.start(), slot);
        next = next.add(slot.extent());
        return slot.start();
    }

    /** The first address after every static slot; seals the space. */
    public BigInteger end() {
        sealed = true;
        return next;
    }

    /** The slot containing {@code address}, or null when no static object covers it. */
    public Slot slotAt(BigInteger address) {
        final Map.Entry<BigInteger, Slot> entry = byStart.floorEntry(address);
        if (entry == null) {
            return null;
        }
        final Slot slot = entry.getValue();
        return address.compareTo(slot.start().add(slot.extent())) < 0 ? slot : null;
    }

    public Collection<Slot> slots() {
        return Collections.unmodifiableCollection(byId.values());
    }
}
