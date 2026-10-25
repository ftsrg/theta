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
package hu.bme.mit.theta.common.visualization;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

/** The colors must be the ones java.awt.Color gave, so that visualizations stay the same. */
public class ColorTest {

    private static String rgb(final java.awt.Color c) {
        return String.format("#%02X%02X%02X", c.getRed(), c.getGreen(), c.getBlue());
    }

    @Test
    public void constantsMatchAwt() {
        assertEquals(rgb(java.awt.Color.WHITE), Color.WHITE.toString());
        assertEquals(rgb(java.awt.Color.BLACK), Color.BLACK.toString());
        assertEquals(rgb(java.awt.Color.LIGHT_GRAY), Color.LIGHT_GRAY.toString());
        assertEquals(rgb(java.awt.Color.RED), Color.RED.toString());
        assertEquals(rgb(java.awt.Color.GREEN), Color.GREEN.toString());
        assertEquals(rgb(java.awt.Color.BLUE), Color.BLUE.toString());
        assertEquals(rgb(java.awt.Color.YELLOW), Color.YELLOW.toString());
    }

    @Test
    public void hsbMatchesAwt() {
        for (int h = -10; h <= 30; h++) {
            for (int s = 0; s <= 10; s++) {
                for (int b = 0; b <= 10; b++) {
                    final float hue = h / 13f;
                    final float saturation = s / 10f;
                    final float brightness = b / 10f;
                    assertEquals(
                            rgb(java.awt.Color.getHSBColor(hue, saturation, brightness)),
                            Color.getHSBColor(hue, saturation, brightness).toString(),
                            "h=" + hue + " s=" + saturation + " b=" + brightness);
                }
            }
        }
    }
}
