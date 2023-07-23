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

import java.io.ByteArrayOutputStream

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
plugins {
    id("cpp-library")
}

fun llvmConfigFlags(vararg args: String): Array<String> {
    val process = ProcessBuilder("llvm-config", *args).start()
    val outputStream = ByteArrayOutputStream()
    process.inputStream.copyTo(outputStream)
    process.waitFor()
    val ret =  outputStream.toString()
        .trim()
        .split(" ")
        .filter { it.length > 1 }
        .map { it.trim() }
        .toTypedArray()
    return ret
}

library {
    targetMachines.add(machines.linux.x86_64)
    tasks.withType(CppCompile::class) {
        compilerArgs.addAll(listOf(
            "-Wall",
            "-fpic",
            "-I/usr/lib/jvm/java-17-openjdk/include/",
            "-I/usr/lib/jvm/java-17-openjdk/include/linux/",
            *llvmConfigFlags("--cxxflags")))
    }

    tasks.register("copyLinkedFile", Copy::class) {
        tasks.withType(LinkSharedLibrary::class).forEach {
            val linkedFile = it.linkedFile.get().asFile
            val targetFolder = rootProject.rootDir.resolve("lib")

            from(linkedFile.parent)
            into(targetFolder)
            include(linkedFile.name)
        }
    }

    tasks.withType(LinkSharedLibrary::class) {
        linkerArgs.addAll(listOf(
            "-rdynamic",
            *llvmConfigFlags("--cxxflags", "--ldflags", "--libs", "core", "bitreader"),
            "-ldl"))
        finalizedBy("copyLinkedFile")
    }
}