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

package hu.bme.mit.theta.frontend.svlib;

import hu.bme.mit.theta.xcfa.model.MetaData;
import org.jetbrains.annotations.NotNull;

public class SvLibMetadata extends MetaData {

  private final String sourceName;
  private final String tag;

  public SvLibMetadata(String sourceName) {
    this(sourceName, null);
  }

  public SvLibMetadata(String sourceName, String tag) {
    this.sourceName = sourceName;
    this.tag = tag;
  }

  @Override
  @NotNull
  public MetaData combine(@NotNull MetaData other) {
    return isTag() || !other.isSubstantial() ? this : other;
  }

  @Override
  public boolean isSubstantial() {
    return isTag();
  }

  public String getSourceName() {
    return sourceName;
  }

  public String getTag() {
    return tag;
  }

  public boolean isTag() {
    return tag != null;
  }
}
