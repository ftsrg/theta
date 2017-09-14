/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.formalism.sts.aiger;

import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.formalism.sts.STS;

public class AIGERLoaderTest {

	@Test
	public void testAIGERLoader() throws IOException {
		AigerParser loader = null;
		// loader = new AIGERLoaderSimple();
		loader = new CompactingAigerParser();
		final STS sts = loader.parse("src/test/resources/simple3.aag");
		System.out.println(sts);
	}

}
