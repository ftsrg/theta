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

package hu.bme.mit.theta.core.utils.indexings;

public class VarIndexingFactory {

    public static PushPopVarIndexing pushPopIndexing(final int defaultOffset) {
        return PushPopVarIndexing.all(defaultOffset);
    }

    public static BasicVarIndexing basicVarIndexing(final int defaultOffset) {
        return BasicVarIndexing.all(defaultOffset);
    }

    public static VarIndexing indexing(final int defaultOffset) {
        return basicVarIndexing(defaultOffset);
    }

    public static PushPopVarIndexing.PushPopVarIndexingBuilder pushPopIndexingBuilder(
            final int defaultOffset) {
        return PushPopVarIndexing.builder(defaultOffset);
    }

    public static BasicVarIndexing.BasicVarIndexingBuilder basicIndexingBuilder(
            final int defaultOffset) {
        return BasicVarIndexing.builder(defaultOffset);
    }

    public static VarIndexingBuilder indexingBuilder(final int defaultOffset) {
        return basicIndexingBuilder(defaultOffset);
    }
}
