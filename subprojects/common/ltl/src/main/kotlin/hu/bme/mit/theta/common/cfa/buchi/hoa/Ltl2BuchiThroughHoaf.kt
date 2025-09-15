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
package hu.bme.mit.theta.common.cfa.buchi.hoa

import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.common.cfa.buchi.Ltl2BuchiTransformer
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarLexer
import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarParser
import jhoafparser.parser.HOAFParser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

class Ltl2BuchiThroughHoaf(private val converter: Ltl2Hoaf, private val logger: Logger) :
  Ltl2BuchiTransformer {

  override fun transform(ltl: String, namedVariables: Map<String, VarDecl<*>>): CFA {
    val variables = namedVariables.values
    val modelContext =
      LTLGrammarParser(CommonTokenStream(LTLGrammarLexer(CharStreams.fromString(ltl)))).model()
    val enumTypes: Map<String, EnumType> =
      variables.mapNotNull { it.type as? EnumType }.associateBy { it.name }
    val toStringVisitor = ToStringVisitor(APGeneratorVisitor(namedVariables, enumTypes))
    val swappedLtl = toStringVisitor.visitModel(modelContext)
    val negatedLtl = "!($swappedLtl)"
    val hoafExpression = converter.transform(negatedLtl)
    val buchiBuilder = BuchiBuilder(logger, toStringVisitor.aps)
    HOAFParser.parseHOA(hoafExpression.byteInputStream(), buchiBuilder)
    return buchiBuilder.build()
  }
}
