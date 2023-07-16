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

package hu.bme.mit.theta.frontend;

import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType;
import hu.bme.mit.theta.frontend.transformation.CStmtCounter;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseOption;

public class ParseContext {
    private final FrontendMetadata metadata;
    private final CStmtCounter cStmtCounter;
    private BitwiseOption bitwiseOption;
    private ArchitectureType architecture = ArchitectureType.ILP32;
    private Boolean multiThreading = false;
    private ArithmeticType arithmetic = ArithmeticType.efficient;

    public ParseContext() {
        metadata = new FrontendMetadata();
        cStmtCounter = new CStmtCounter();
    }

    public FrontendMetadata getMetadata() {
        return metadata;
    }

    public BitwiseOption getBitwiseOption() {
        return bitwiseOption;
    }

    public void setBitwiseOption(BitwiseOption bitwiseOption) {
        this.bitwiseOption = bitwiseOption;
    }

    public ArchitectureType getArchitecture() {
        return architecture;
    }

    public void setArchitecture(ArchitectureType architecture) {
        this.architecture = architecture;
    }

    public Boolean getMultiThreading() {
        return multiThreading;
    }

    public void setMultiThreading(Boolean multiThreading) {
        this.multiThreading = multiThreading;
    }

    public ArithmeticType getArithmetic() {
        return arithmetic;
    }

    public void setArithmetic(ArithmeticType arithmetic) {
        this.arithmetic = arithmetic;
    }

    public CStmtCounter getCStmtCounter() {
        return cStmtCounter;
    }
}
