/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.cli

import com.beust.jcommander.JCommander
import com.beust.jcommander.Parameter
import com.beust.jcommander.ParameterException
import com.google.gson.JsonIOException
import com.google.gson.JsonSyntaxException
import hu.bme.mit.theta.common.CliUtils
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.UniqueWarningLogger
import hu.bme.mit.theta.xcfa.cli.params.ExitCodes
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getGson
import java.io.File
import java.io.FileReader
import kotlin.system.exitProcess


class XcfaCli(private val args: Array<String>) {

    @Parameter(names = ["--config", "-c"], description = "Configuration file (CLI options will overwrite these!)")
    var configFile: File? = null

    @Parameter(names = ["--help", "-h"], help = true)
    private var help = false

    @Parameter(names = ["--svcomp"])
    private var svcomp = false

    @Parameter
    var remainingFlags: MutableList<String> = ArrayList()

    private fun run() {
        lateinit var config: XcfaConfig<*, *>
        /// Checking flags
        try {
            JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(*args)
            val configFile = this.configFile
            if (configFile != null) {
                config = getGson().fromJson(FileReader(configFile), XcfaConfig::class.java)
            } else {
                config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
            }
            if (svcomp) {
                remainingFlags.addAll(
                    listOf(
                        "--enable-output",
                        "--disable-xcfa-serialization",
                        "--disable-arg-generation",
                        "--disable-chc-serialization",
                        "--disable-c-serialization",
                        "--only-svcomp-witness"
                    )
                )
            }
            while (remainingFlags.isNotEmpty()) {
                val nextArgs = remainingFlags.toTypedArray()
                remainingFlags.clear()
                val builder = JCommander.newBuilder().addObject(this)
                for (obj in config.getObjects()) {
                    builder.addObject(obj)
                }
                builder.programName(JAR_NAME).build().parse(*nextArgs)
                if (!config.update() && remainingFlags.isNotEmpty()) {
                    throw ParameterException("Extraneous parameters: $remainingFlags")
                }
            }
        } catch (ex: ParameterException) {
            println("Invalid parameters, details:")
            ex.printStackTrace()
            ex.usage()
            exitProcess(ExitCodes.INVALID_PARAM.code)
        } catch (ex: JsonIOException) {
            println("There was a problem reading from ${configFile}:")
            ex.printStackTrace()
            exitProcess(ExitCodes.INVALID_PARAM.code)
        } catch (ex: JsonSyntaxException) {
            println("There was a problem parsing ${configFile}:")
            ex.printStackTrace()
            exitProcess(ExitCodes.INVALID_PARAM.code)
        }


        if (help) {
            val builder = JCommander.newBuilder().addObject(this)
            for (obj in config.getObjects()) {
                builder.addObject(obj)
            }
            builder.build().usage()
            return
        }

        /// version
        if (config.outputConfig.versionInfo) {
            CliUtils.printVersion(System.out)
            return
        }

        val logger = ConsoleLogger(config.debugConfig.logLevel)
        val uniqueLogger = UniqueWarningLogger(logger)

        runConfig(config, logger, uniqueLogger, false)
    }


    companion object {

        private const val JAR_NAME = "theta-xcfa-cli.jar"

        @JvmStatic
        fun main(args: Array<String>) {
            val mainApp = XcfaCli(args)
            mainApp.run()
        }
    }
}
