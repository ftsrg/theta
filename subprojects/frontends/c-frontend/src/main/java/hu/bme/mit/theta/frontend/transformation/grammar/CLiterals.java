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
package hu.bme.mit.theta.frontend.transformation.grammar;

import java.util.ArrayList;
import java.util.List;

/**
 * Decoding of C character and string literals. Shared so that {@code '\n'} and {@code "\n"} cannot
 * disagree: the two used to be decoded by separate ad-hoc code, and the character one got every
 * escape family wrong -- {@code '\x41'} was read as *octal* 41, {@code '\101'} as *decimal* 101, and
 * any single-letter escape ({@code '\n'}, {@code '\t'}, {@code '\\'}) threw NumberFormatException
 * out of the frontend.
 */
public final class CLiterals {

    private CLiterals() {}

    /**
     * The byte values of a string literal's contents, with the enclosing quotes (and any encoding
     * prefix) already stripped. Escapes are decoded; a line continuation contributes no byte.
     */
    public static List<Integer> stringBytes(String body) {
        final List<Integer> bytes = new ArrayList<>();
        int i = 0;
        while (i < body.length()) {
            final char c = body.charAt(i++);
            if (c != '\\' || i >= body.length()) {
                bytes.add(c & 0xFF);
                continue;
            }
            final int[] decoded = escapeAt(body, i);
            i = decoded[1];
            if (decoded[0] >= 0) {
                bytes.add(decoded[0] & 0xFF);
            }
        }
        return bytes;
    }

    /**
     * The value of a character constant, quotes included ({@code 'a'}, {@code '\n'}, {@code '\x41'},
     * {@code '\101'}), or {@code null} if [text] is not one.
     *
     * <p>A multi-character constant ({@code 'ab'}, and the {@code 'MAGI'} four-character tags that
     * file-format code uses) is implementation-defined; the bytes are packed big-endian into an int,
     * which is what gcc does.
     */
    public static Integer charValue(String text) {
        // An encoding prefix (`L'a'`, `u'a'`, `U'a'`) is dropped: the value of the character is the
        // same, and the frontend has no wider character type to put it in anyway.
        final int open = text.indexOf('\'');
        if (open < 0 || open > 2 || text.length() < open + 3 || !text.endsWith("'")) {
            return null;
        }
        if (!text.substring(0, open).matches("[LuU]?")) {
            return null;
        }
        final List<Integer> bytes = stringBytes(text.substring(open + 1, text.length() - 1));
        if (bytes.isEmpty()) {
            return null;
        }
        int value = 0;
        for (int b : bytes) {
            value = (value << 8) | (b & 0xFF);
        }
        return value;
    }

    /**
     * Decodes the escape whose backslash sits just before [start], as {@code {value, nextIndex}}. A
     * value of {@code -1} means the escape stands for no character at all (a line continuation).
     */
    private static int[] escapeAt(String body, int start) {
        int i = start;
        final char escape = body.charAt(i++);
        switch (escape) {
            case 'n':
                return new int[] {10, i};
            case 't':
                return new int[] {9, i};
            case 'r':
                return new int[] {13, i};
            case 'a':
                return new int[] {7, i};
            case 'b':
                return new int[] {8, i};
            case 'f':
                return new int[] {12, i};
            case 'v':
                return new int[] {11, i};
            case 'e':
                return new int[] {27, i}; // GNU extension
            case '\n':
                return new int[] {-1, i};
            case '\r':
                if (i < body.length() && body.charAt(i) == '\n') {
                    i++;
                }
                return new int[] {-1, i};
            case 'x':
                {
                    int value = 0;
                    while (i < body.length() && Character.digit(body.charAt(i), 16) >= 0) {
                        value = value * 16 + Character.digit(body.charAt(i++), 16);
                    }
                    return new int[] {value, i};
                }
            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
                {
                    int value = escape - '0';
                    for (int digits = 1;
                            digits < 3
                                    && i < body.length()
                                    && body.charAt(i) >= '0'
                                    && body.charAt(i) <= '7';
                            digits++) {
                        value = value * 8 + (body.charAt(i++) - '0');
                    }
                    return new int[] {value, i};
                }
            default:
                // \\ \' \" \? and anything unrecognised: the character stands for itself.
                return new int[] {escape, i};
        }
    }
}
