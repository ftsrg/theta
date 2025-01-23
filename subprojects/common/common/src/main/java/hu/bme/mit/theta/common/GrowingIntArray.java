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
package hu.bme.mit.theta.common;

public class GrowingIntArray {
    private final int defaultSize;
    private final int growingAmount;

    private int lastIndex;

    private int[] array;

    public GrowingIntArray() {
        this(100, 100);
    }

    public GrowingIntArray(int defaultSize, int growingAmount) {
        this.defaultSize = defaultSize;
        this.growingAmount = growingAmount;
        this.array = new int[defaultSize];
        this.lastIndex = -1;
    }

    public int get(int index) {
        if (index <= lastIndex) return array[index];
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getSize() {
        return lastIndex + 1;
    }

    public void add(int value) {
        if (lastIndex >= array.length - 1) {
            grow();
        }
        array[lastIndex + 1] = value;
        lastIndex++;
    }

    private void grow() {
        int[] newArray = new int[array.length + growingAmount];
        System.arraycopy(array, 0, newArray, 0, array.length);
        array = newArray;
    }
}
