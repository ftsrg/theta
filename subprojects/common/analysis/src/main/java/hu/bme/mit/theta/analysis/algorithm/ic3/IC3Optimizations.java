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

package hu.bme.mit.theta.analysis.algorithm.ic3;

public class IC3Optimizations {


  public boolean isUnSatOpt() {
    return unSatOpt;
  }

  public boolean isNotBOpt() {
    return notBOpt;
  }

  public boolean isPropagateOpt() {
    return propagateOpt;
  }

  public boolean isGeneralizeOpt() {
    return generalizeOpt;
  }

  public boolean isFilterOpt() {
    return filterOpt;
  }


  public boolean isPropertyOpt() {
    return propertyOpt;
  }


  private final boolean unSatOpt;
  private final boolean notBOpt;
  private final boolean propagateOpt;
  private final boolean filterOpt;
  private final boolean propertyOpt;
  private final boolean generalizeOpt;



  public IC3Optimizations(boolean unSatOpt, boolean notBOpt, boolean propagateOpt, boolean filterOpt, boolean MICOpt, boolean propertyOpt) {
    this.unSatOpt = unSatOpt;
    this.notBOpt = notBOpt;
    this.propagateOpt = propagateOpt;
    this.filterOpt = filterOpt;
    this.propertyOpt = propertyOpt;
    this.generalizeOpt = MICOpt;
  }
}
