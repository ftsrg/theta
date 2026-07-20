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
package hu.bme.mit.theta.frontend.transformation.grammar.type;

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout;
import java.util.List;

/**
 * Reads the two GCC attributes that change an object's layout out of the attribute lists the
 * grammar already parses: {@code packed} and {@code aligned(n)}.
 *
 * <p>Every other attribute stays ignored, which is the long-standing behaviour -- they describe
 * things this frontend does not model. These two are different only because {@link ObjectLayout}
 * cannot compute correct offsets without them: a packed struct laid out unpacked puts every member
 * after the first in the wrong place.
 *
 * <p>GCC spells both with and without underscores ({@code packed}, {@code __packed__}), and CIL
 * emits either, so both are accepted.
 */
public final class LayoutAttributes {

    private LayoutAttributes() {}

    /** The layout attributes in [specifiers], merged; {@code NONE} when there are none. */
    public static ObjectLayout.Attributes of(
            List<CParser.GccAttributeSpecifierContext> specifiers) {
        if (specifiers == null || specifiers.isEmpty()) {
            return ObjectLayout.Attributes.NONE;
        }
        boolean packed = false;
        int alignedToBits = 0;
        for (CParser.GccAttributeSpecifierContext specifier : specifiers) {
            if (specifier.gccAttributeList() == null) {
                continue;
            }
            for (CParser.GccAttributeContext attribute : specifier.gccAttributeList().gccAttribute()) {
                if (attribute == null || attribute.getChildCount() == 0) {
                    continue;
                }
                final String name = normalize(attribute.getChild(0).getText());
                if (name.equals("packed")) {
                    packed = true;
                } else if (name.equals("aligned")) {
                    final int bits = alignmentBits(attribute);
                    if (bits > alignedToBits) {
                        alignedToBits = bits;
                    }
                }
            }
        }
        return packed || alignedToBits > 0
                ? new ObjectLayout.Attributes(packed, alignedToBits)
                : ObjectLayout.Attributes.NONE;
    }

    /** `__packed__` and `packed` are the same attribute. */
    private static String normalize(String name) {
        String result = name;
        if (result.startsWith("__") && result.endsWith("__") && result.length() > 4) {
            result = result.substring(2, result.length() - 2);
        }
        return result;
    }

    /**
     * The alignment {@code aligned(n)} asks for, in bits, or 0 when it cannot be read.
     *
     * <p>The argument is a byte count. A bare {@code aligned} with no argument means "the largest
     * alignment this target ever needs", which is 16 bytes on both models GCC targets here.
     * Anything that is not a plain integer literal (a {@code sizeof}, an unexpanded macro) is
     * skipped rather than guessed: a wrong alignment is a wrong offset for every later member, and
     * ignoring the attribute at least keeps the natural layout.
     */
    private static int alignmentBits(CParser.GccAttributeContext attribute) {
        final var arguments = attribute.argumentExpressionList();
        if (arguments == null) {
            return 128; // bare `aligned`: __BIGGEST_ALIGNMENT__
        }
        final String text = arguments.getText().trim();
        try {
            final int bytes = Integer.parseInt(text);
            // Alignments are powers of two; anything else is a misparse, not an alignment.
            return bytes > 0 && (bytes & (bytes - 1)) == 0 ? bytes * 8 : 0;
        } catch (NumberFormatException e) {
            return 0;
        }
    }
}
