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

/**
 * An RGB color of a visualized node or edge. Used instead of {@code java.awt.Color}, whose class
 * initialization loads the AWT native library.
 */
public final class Color {

    public static final Color WHITE = new Color(255, 255, 255);
    public static final Color BLACK = new Color(0, 0, 0);
    public static final Color LIGHT_GRAY = new Color(192, 192, 192);
    public static final Color RED = new Color(255, 0, 0);
    public static final Color GREEN = new Color(0, 255, 0);
    public static final Color BLUE = new Color(0, 0, 255);
    public static final Color YELLOW = new Color(255, 255, 0);

    private final int red;
    private final int green;
    private final int blue;

    public Color(final int red, final int green, final int blue) {
        this.red = checkComponent(red);
        this.green = checkComponent(green);
        this.blue = checkComponent(blue);
    }

    private static int checkComponent(final int value) {
        if (value < 0 || value > 255) {
            throw new IllegalArgumentException("Color component out of range: " + value);
        }
        return value;
    }

    /**
     * The color of hue {@code hue} (in turns: only its fractional part counts), saturation and
     * brightness (both in [0, 1]), with the same rounding as {@code java.awt.Color.getHSBColor}.
     */
    public static Color getHSBColor(
            final float hue, final float saturation, final float brightness) {
        if (saturation == 0) {
            final int gray = toComponent(brightness);
            return new Color(gray, gray, gray);
        }
        final float sector = (hue - (float) Math.floor(hue)) * 6.0f;
        final float offset = sector - (float) Math.floor(sector);
        final float min = brightness * (1.0f - saturation);
        final float falling = brightness * (1.0f - saturation * offset);
        final float rising = brightness * (1.0f - saturation * (1.0f - offset));
        return switch ((int) sector) {
            case 0 -> of(brightness, rising, min);
            case 1 -> of(falling, brightness, min);
            case 2 -> of(min, brightness, rising);
            case 3 -> of(min, falling, brightness);
            case 4 -> of(rising, min, brightness);
            default -> of(brightness, min, falling);
        };
    }

    private static Color of(final float red, final float green, final float blue) {
        return new Color(toComponent(red), toComponent(green), toComponent(blue));
    }

    private static int toComponent(final float value) {
        return (int) (value * 255.0f + 0.5f);
    }

    public int getRed() {
        return red;
    }

    public int getGreen() {
        return green;
    }

    public int getBlue() {
        return blue;
    }

    @Override
    public boolean equals(final Object obj) {
        return obj instanceof Color that
                && red == that.red
                && green == that.green
                && blue == that.blue;
    }

    @Override
    public int hashCode() {
        return (red << 16) | (green << 8) | blue;
    }

    @Override
    public String toString() {
        return String.format("#%02X%02X%02X", red, green, blue);
    }
}
