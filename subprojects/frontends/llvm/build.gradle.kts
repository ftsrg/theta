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

import org.gradle.internal.os.OperatingSystem.current
import java.io.ByteArrayOutputStream
import java.io.IOException

plugins {
    id("cpp-library")
}

/**
 * This subproject builds the lib/libtheta-llvm.so if the necessary pre-requisites are met (LLVM-15 is available)
 */

val llvmConfigBinary by lazy {
  try {
    val output = runCommandForOutput("llvm-config", "--version")
    val version = output[0].split('.')
    val major = version[0]
    val minor = version[1]
    val patch = version[2]
    if (major == "15")
      "llvm-config"
    else
      throw IOException()
  } catch (e: IOException) {
    try {
      val output = runCommandForOutput("llvm-config-15", "--version")
      val version = output[0].split('.')
      val major = version[0]
      val minor = version[1]
      val patch = version[2]
      if (major == "15")
        "llvm-config-15"
      else
        throw IOException()
    } catch (e: IOException) {
      println("LLVM-15 not installed, not building native library.")
      null
    }
  }
}

val clangBinary by lazy {
  try {
    val output = runCommandForOutput("clang", "--version")
    var version: List<String> = listOf(output.joinToString(" "))
    for (token in output) {
      val tryVersion = token.split('.')
      if (tryVersion.size == 3 && tryVersion.all { it.all(Char::isDigit) }) {
        version = tryVersion
        break
      }
    }

    val major = version[0]
    if (major == "15") {
      "clang"
    } else {
      println("clang does not point to clang-15, not building native library. Found version: $version")
      null
    }
  } catch (e: IOException) {
    println("clang-15 not installed , not building native library.")
    null
  }
}

val buildNativeLib = project.findProperty("buildLlvmNative")?.toString()?.toBoolean() ?: false
val taskEnabled = buildNativeLib && current().isLinux && llvmConfigBinary != null && clangBinary != null

fun runCommandForOutput(vararg args: String): Array<String> {
    val process = ProcessBuilder(*args).start()
    val outputStream = ByteArrayOutputStream()
    process.inputStream.copyTo(outputStream)
    process.waitFor()
    val ret = outputStream.toString()
        .trim()
        .split(" ", "\n", "\r")
        .filter { it.length > 1 }
        .map { it.trim() }
        .toTypedArray()
    return ret
}

fun llvmConfigFlags(vararg args: String): Array<String> {
    if (!taskEnabled) return arrayOf()
    return try {
        runCommandForOutput(llvmConfigBinary!!, *args)
    } catch (e: IOException) {
        e.printStackTrace()
        arrayOf()
    }
}

fun jniConfigFlags(): Array<String> {
    if (!taskEnabled) return arrayOf()
    val jdkHomeArr = runCommandForOutput("bash", "-c",
        "dirname \$(cd \$(dirname \$(readlink -f \$(which javac) || which javac)); pwd -P)")
    check(jdkHomeArr.size == 1)
    val jdkHome = File(jdkHomeArr[0])
    check(jdkHome.exists())
    val mainInclude = jdkHome.resolve("include")
    val linuxInclude = mainInclude.resolve("linux")
    return arrayOf(
        "-I${mainInclude.absolutePath}",
        "-I${linuxInclude.absolutePath}",
    )
}

library {
    targetMachines.add(machines.linux.x86_64)
    tasks.withType(CppCompile::class) {
        compilerArgs.addAll(listOf(
            "-Wall",
            "-fpic",
            *jniConfigFlags(),
            *llvmConfigFlags("--cxxflags")))
        if (!taskEnabled) {
            enabled = false
        }
    }

    tasks.withType(LinkSharedLibrary::class) {
        linkerArgs.addAll(listOf(
            "-rdynamic",
            *llvmConfigFlags("--cxxflags", "--ldflags", "--libs", "core", "bitreader"),
            "-ldl"))
        if (!taskEnabled) {
            enabled = false
        }
    }
}