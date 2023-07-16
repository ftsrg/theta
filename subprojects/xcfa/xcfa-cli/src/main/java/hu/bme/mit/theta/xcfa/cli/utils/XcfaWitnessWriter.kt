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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.witnesses.Witness
import hu.bme.mit.theta.xcfa.cli.witnesses.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.cli.witnesses.traceToWitness
import java.io.BufferedWriter
import java.io.File
import java.io.FileWriter
import java.io.IOException
import java.nio.file.FileSystems
import java.nio.file.Path
import java.text.DateFormat
import java.text.SimpleDateFormat
import java.util.*

class XcfaWitnessWriter {

    fun writeWitness(
        safetyResult: SafetyResult<*, *>,
        inputFile: File,
        cexSolverFactory: SolverFactory,
        parseContext: ParseContext
    ) {
        if (safetyResult.isUnsafe) {
            val workdir: Path = FileSystems.getDefault().getPath("").toAbsolutePath()
            val witnessfile = File(workdir.toString() + File.separator + "witness.graphml")
            val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> = XcfaTraceConcretizer.concretize(
                safetyResult.asUnsafe().trace as Trace<XcfaState<*>, XcfaAction>?, cexSolverFactory)

            val witnessTrace = traceToWitness(trace = concrTrace, parseContext = parseContext)
            val witness = Witness(witnessTrace, inputFile)
            val xml = witness.toPrettyXml()
            witnessfile.writeText(xml)
        } else if (safetyResult.isSafe) {
            val workdir = FileSystems.getDefault().getPath("").toAbsolutePath()
            val witnessfile = File(workdir.toString() + File.separator + "witness.graphml")

            val taskHash = WitnessWriter.createTaskHash(inputFile.absolutePath)
            val dummyWitness = StringBuilder()
            dummyWitness.append(
                "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">")
                .append(System.lineSeparator()).append(
                    "<key id=\"sourcecodelang\" attr.name=\"sourcecodelang\" for=\"graph\"/>")
                .append(System.lineSeparator()).append(
                    "<key id=\"witness-type\" attr.name=\"witness-type\" for=\"graph\"/>")
                .append(System.lineSeparator()).append(
                    "<key id=\"entry\" attr.name=\"entry\" for=\"node\">")
                .append(System.lineSeparator()).append(
                    "<default>false</default>").append(System.lineSeparator()).append(
                    "</key>").append(System.lineSeparator()).append(
                    "<key id=\"invariant\" attr.name=\"invariant\" for=\"node\">")
                .append(System.lineSeparator()).append(
                    "<default>false</default>").append(System.lineSeparator()).append(
                    "</key>").append(System.lineSeparator()).append(
                    "<key attr.name=\"specification\" attr.type=\"string\" for=\"graph\" id=\"specification\"/>")
                .append(System.lineSeparator()).append(
                    "<key attr.name=\"producer\" attr.type=\"string\" for=\"graph\" id=\"producer\"/>")
                .append(System.lineSeparator()).append(
                    "<key attr.name=\"programFile\" attr.type=\"string\" for=\"graph\" id=\"programfile\"/>")
                .append(System.lineSeparator()).append(
                    "<key attr.name=\"programHash\" attr.type=\"string\" for=\"graph\" id=\"programhash\"/>")
                .append(System.lineSeparator()).append(
                    "<key attr.name=\"architecture\" attr.type=\"string\" for=\"graph\" id=\"architecture\"/>")
                .append(System.lineSeparator()).append(
                    "<key attr.name=\"creationtime\" attr.type=\"string\" for=\"graph\" id=\"creationtime\"/>")
                .append(System.lineSeparator()).append(
                    "<graph edgedefault=\"directed\">").append(System.lineSeparator()).append(
                    "<data key=\"witness-type\">correctness_witness</data>")
                .append(System.lineSeparator()).append(
                    "<data key=\"producer\">theta</data>").append(System.lineSeparator()).append(
                    "<data key=\"specification\">CHECK( init(main()), LTL(G ! call(reach_error())) )</data>")
                .append(System.lineSeparator()).append(
                    "<data key=\"sourcecodelang\">C</data>").append(System.lineSeparator()).append(
                    "<data key=\"architecture\">32bit</data>").append(System.lineSeparator())
                .append(
                    "<data key=\"programhash\">")
            dummyWitness.append(taskHash)
            dummyWitness.append("</data>").append(System.lineSeparator()).append(
                "<data key=\"creationtime\">")

            val tz: TimeZone = TimeZone.getTimeZone("UTC")
            val df: DateFormat = SimpleDateFormat(
                "yyyy-MM-dd'T'HH:mm:ss'Z'") // Quoted "Z" to indicate UTC, no timezone offset

            df.timeZone = tz
            val isoDate: String = df.format(Date())

            dummyWitness.append(isoDate)
            dummyWitness.append("</data>").append(System.lineSeparator()).append(
                "<data key=\"programfile\">")
            dummyWitness.append(inputFile.name)
            dummyWitness.append("</data>").append(System.lineSeparator()).append(
                "<node id=\"N0\">").append(System.lineSeparator()).append(
                "<data key=\"entry\">true</data>").append(System.lineSeparator()).append(
                "</node>").append(System.lineSeparator()).append(
                "</graph>").append(System.lineSeparator()).append(
                "</graphml>")

            try {
                BufferedWriter(FileWriter(witnessfile)).use { bw ->
                    bw.write(dummyWitness.toString())
                }
            } catch (ioe: IOException) {
                ioe.printStackTrace()
            }
        }
    }
}