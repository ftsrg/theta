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
package hu.bme.mit.theta.frontend.petrinet.pnml;

import fr.lip6.move.pnml.framework.hlapi.HLAPIRootClass;
import fr.lip6.move.pnml.framework.utils.PNMLUtils;
import fr.lip6.move.pnml.ptnet.hlapi.PetriNetDocHLAPI;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import java.io.File;
import java.util.List;
import java.util.Objects;

public final class PetriNetParser {
    public static enum PetriNetType {
        PTNet,
        Other
    }

    private final HLAPIRootClass root;

    public static PetriNetParser loadPnml(File file) throws Exception {
        final HLAPIRootClass root = PNMLUtils.importPnmlDocument(file, false);
        return new PetriNetParser(root);
    }

    private PetriNetParser(final HLAPIRootClass root) {
        this.root = Objects.requireNonNull(root);
    }

    public PetriNetType getPetriNetType() {
        if (root instanceof PetriNetDocHLAPI) {
            return PetriNetType.PTNet;
        }
        return PetriNetType.Other;
    }

    public List<PetriNet> parsePTNet() throws PnmlParseException {
        if (root instanceof PetriNetDocHLAPI) {
            return new Lip6PnmlToPetrinet((PetriNetDocHLAPI) root).parse();
        }
        throw new PnmlParseException("The file was not a P/T Net.");
    }
}
