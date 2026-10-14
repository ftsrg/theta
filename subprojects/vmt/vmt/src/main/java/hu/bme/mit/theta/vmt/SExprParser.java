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
package hu.bme.mit.theta.vmt;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

/** Reads SMT-LIB text into top-level s-expressions, without interpreting any of them. */
public final class SExprParser {

    private final String input;
    private int pos = 0;

    private SExprParser(String input) {
        this.input = input;
    }

    public static List<SExpr> parseAll(String input) {
        return new SExprParser(input).parseAll();
    }

    private List<SExpr> parseAll() {
        final List<SExpr> result = new ArrayList<>();
        final Deque<List<SExpr>> stack = new ArrayDeque<>();
        while (true) {
            skipWhitespaceAndComments();
            if (pos >= input.length()) break;
            final char c = input.charAt(pos);
            if (c == '(') {
                pos++;
                stack.push(new ArrayList<>());
            } else if (c == ')') {
                if (stack.isEmpty()) throw error("Unbalanced ')'");
                pos++;
                final SExpr list = new SExpr.SList(stack.pop());
                if (stack.isEmpty()) result.add(list);
                else stack.peek().add(list);
            } else {
                final SExpr atom = new SExpr.Atom(readAtom());
                if (stack.isEmpty()) result.add(atom);
                else stack.peek().add(atom);
            }
        }
        if (!stack.isEmpty()) throw error("Unbalanced '(' at end of input");
        return result;
    }

    private void skipWhitespaceAndComments() {
        while (pos < input.length()) {
            final char c = input.charAt(pos);
            if (Character.isWhitespace(c)) {
                pos++;
            } else if (c == ';') {
                while (pos < input.length() && input.charAt(pos) != '\n') pos++;
            } else {
                return;
            }
        }
    }

    private String readAtom() {
        final int start = pos;
        final char c = input.charAt(pos);
        if (c == '|') {
            final int end = input.indexOf('|', pos + 1);
            if (end < 0) throw error("Unterminated quoted symbol");
            pos = end + 1;
        } else if (c == '"') {
            pos++;
            while (true) {
                if (pos >= input.length()) throw error("Unterminated string literal");
                if (input.charAt(pos) == '"') {
                    // "" is an escaped quote inside an SMT-LIB string
                    if (pos + 1 < input.length() && input.charAt(pos + 1) == '"') pos += 2;
                    else {
                        pos++;
                        break;
                    }
                } else pos++;
            }
        } else {
            while (pos < input.length()) {
                final char d = input.charAt(pos);
                if (Character.isWhitespace(d)
                        || d == '('
                        || d == ')'
                        || d == ';'
                        || d == '|'
                        || d == '"') break;
                pos++;
            }
        }
        return input.substring(start, pos);
    }

    private VmtParseException error(String message) {
        return new VmtParseException(message + " (offset " + pos + ")");
    }
}
