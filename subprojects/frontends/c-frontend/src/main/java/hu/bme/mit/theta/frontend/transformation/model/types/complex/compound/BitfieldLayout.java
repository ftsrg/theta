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
package hu.bme.mit.theta.frontend.transformation.model.types.complex.compound;

import java.util.ArrayList;
import java.util.List;

/**
 * The storage-unit layout of a struct's members, packing consecutive bitfields into shared cells.
 *
 * <p>Theta models a struct member access as {@code __arrays_T[base][unitIndex]} -- one cell per
 * <em>storage unit</em>, not one per member. For ordinary members that is one cell each (unit
 * index == member position, the historical behaviour). Consecutive bitfield members instead pack
 * into a single unit while they fit in that unit's base-type width, so the number of cells matches
 * the byte layout the program allocates for: {@code struct A { unsigned char a; unsigned char b:2;
 * unsigned char c:2; unsigned char d:4; }} occupies 2 cells (a, then b/c/d packed), so {@code
 * malloc(2)} is sufficient -- the field-index-vs-byte-size mismatch that makes the fourth member
 * of a packed struct look like an out-of-bounds access.
 *
 * <p>This is the pure layout computation only; it does not yet drive {@code memberOffset} or the
 * bit-slice access/assignment lowering (see PLAN.md batch 43-design). It is exercised directly by
 * {@code BitfieldLayoutTest}.
 */
public final class BitfieldLayout {

    private BitfieldLayout() {}

    /**
     * One struct member's input to the layout: the bit width of its declared base type, and its
     * bitfield width ({@code -1} for an ordinary, non-bitfield member). A named zero-width bitfield
     * is a unit boundary that carries no storage; unnamed bitfields (which have no field at all)
     * must be dropped by the caller before layout.
     */
    public record Member(int baseBits, int bitfieldWidth) {
        public boolean isBitfield() {
            return bitfieldWidth >= 0;
        }
    }

    /**
     * Where one member lives: the index of the shared storage cell, the member's bit offset within
     * that cell ({@code 0} for ordinary members), its width in bits, and whether it is a bitfield
     * (so the access lowering knows to slice). A named zero-width bitfield produces no slot.
     */
    public record Slot(int unitIndex, int bitOffset, int width, boolean bitfield) {}

    /** The computed layout: one {@link Slot} per member (in order), and the total cell count. */
    public record Layout(List<Slot> slots, int unitCount) {}

    /**
     * Assigns each member a storage unit. Ordinary members each take their own unit; a run of
     * bitfields shares one unit until the next would overflow that unit's base-type width (or an
     * ordinary member / a zero-width bitfield breaks the run), at which point a fresh unit starts.
     * The layout never straddles a bitfield across two units -- the common CIL/gcc `-O0` shape, and
     * all the memory model needs to keep the cell count at or below the byte size.
     */
    public static Layout compute(List<Member> members) {
        final List<Slot> slots = new ArrayList<>(members.size());
        int unit = -1;
        int bitsUsed = 0;
        int unitBaseBits = 0;
        boolean unitIsBitfield = false;

        for (Member m : members) {
            if (!m.isBitfield()) {
                unit++;
                slots.add(new Slot(unit, 0, m.baseBits(), false));
                unitIsBitfield = false;
                bitsUsed = 0;
                continue;
            }
            final int width = m.bitfieldWidth();
            if (width == 0) {
                // A named zero-width bitfield is a boundary: it closes the current run so the next
                // bitfield starts a new unit, and occupies no storage of its own.
                unitIsBitfield = false;
                bitsUsed = 0;
                continue;
            }
            if (unitIsBitfield && bitsUsed + width <= unitBaseBits) {
                slots.add(new Slot(unit, bitsUsed, width, true));
                bitsUsed += width;
            } else {
                unit++;
                unitBaseBits = m.baseBits();
                bitsUsed = width;
                unitIsBitfield = true;
                slots.add(new Slot(unit, 0, width, true));
            }
        }
        return new Layout(slots, unit + 1);
    }
}
