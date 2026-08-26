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

plugins {
    id("kotlin-common")
    id("kaml-serialization")
    id("cli-tool")
    id("archive-packaging")
}

dependencies {
    implementation(files(rootDir.resolve(Deps.delta)))
    implementation(project(":theta-common"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-c-frontend"))
    implementation(project(":theta-chc-frontend"))
    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-xcfa-analysis"))
    implementation(project(":theta-xcfa2chc"))
    implementation(project(":theta-c2xcfa"))
    implementation(project(":theta-solver-z3"))
    implementation(project(":theta-solver-z3-legacy"))
    implementation(project(":theta-solver-smtlib"))
    testImplementation(testFixtures(project(":theta-solver-smtlib")))
    implementation(project(":theta-solver-javasmt"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-c-frontend"))
    implementation(project(":theta-grammar"))
    implementation(project(":theta-llvm2xcfa"))
    implementation(project(":theta-litmus2xcfa"))
    implementation(project(":theta-graph-solver"))
    implementation(project(":theta-cat"))
    implementation(project(":theta-cfa"))
    implementation(files(rootDir.resolve(Deps.z3legacy)))
    implementation(Deps.z3)
    implementation("com.zaxxer:nuprocess:2.0.5")
    implementation("org.jetbrains.kotlin:kotlin-scripting-jsr223:${Versions.kotlin}")
    implementation(project(":theta-btor2-frontend"))
    implementation(project(":theta-btor2xcfa"))
    testImplementation(kotlin("script-runtime"))
}

application {
    mainClass.set("hu.bme.mit.theta.xcfa.cli.XcfaCli")
}

archivePackaging {
    variant {
        toolName = "Theta-svcomp"
        inputFlags = "--svcomp --portfolio STABLE"
        solvers = listOf("cvc5:1.2.0", "cvc5:1.0.8", "mathsat:5.6.12", "mathsat:5.6.10")
        readmeTemplate = file("src/main/resources/archive-packaging/README-SVCOMP.md")
        smoketestSource = file("src/main/resources/archive-packaging/smoketest.sh")
        inputSource = file("src/main/resources/archive-packaging/input.c")
    }
    variant {
        toolName = "EmergenTheta-svcomp"
        inputFlags = "--svcomp --portfolio EMERGENT"
        solvers = listOf("cvc5:1.2.0", "cvc5:1.0.8", "mathsat:5.6.12", "mathsat:5.6.10")
        readmeTemplate = file("src/main/resources/archive-packaging/README-SVCOMP.md")
        smoketestSource = file("src/main/resources/archive-packaging/smoketest.sh")
        inputSource = file("src/main/resources/archive-packaging/input.c")
    }
    variant {
        toolName = "Thorn-svcomp"
        inputFlags = "--svcomp --porfolio HORN"
        solvers = listOf("z3:4.15.3", "eldarica:2.2", "golem:0.9.0")
        readmeTemplate = file("src/main/resources/archive-packaging/README-SVCOMP.md")
        smoketestSource = file("src/main/resources/archive-packaging/smoketest.sh")
        inputSource = file("src/main/resources/archive-packaging/input.c")
    }
    variant {
        toolName = "Theta-chccomp"
        inputFlags = "--backend PORTFOLIO \\ \n--input-type CHC \\ \n--portfolio CHC-COMP \\ \n--print-model"
        solvers = listOf("cvc5:1.0.8", "mathsat:5.6.10")
        readmeTemplate = file("src/main/resources/archive-packaging/README-CHCCOMP.md")
        scriptName = "chc"
    }
}

// The canary suite (see `canaries/README.md`) as a registered Gradle test task.
//
// Not part of `test`: a sweep takes ~20 minutes and needs a built Theta-svcomp distribution plus a
// local sv-benchmarks checkout, neither of which a fresh clone has. As its own task it stays
// discoverable and reports one JUnit result per canary instead of a single exit code; when the
// prerequisites are missing it skips rather than fails (see CanarySuiteTest).
val canaryTest by
    tasks.registering(Test::class) {
        group = "verification"
        description =
            "Runs the canary suite (real SV-COMP tasks + feature-guard fixtures) against the built " +
                "Theta-svcomp distribution. Set -Ptheta.canary.mode=full to check verdicts rather " +
                "than only that the frontend builds each task."

        testClassesDirs = sourceSets["test"].output.classesDirs
        classpath = sourceSets["test"].runtimeClasspath
        filter { includeTestsMatching("*CanarySuiteTest*") }

        // The suite needs the packaged distribution, not just the classes. Referenced by name
        // because the archive-packaging plugin registers its variants after this block is evaluated.
        dependsOn("buildArchiveTheta-svcomp")

        systemProperty("theta.canary.home", layout.projectDirectory.dir("canaries").asFile.absolutePath)
        systemProperty("theta.canary.repoRoot", rootDir.absolutePath)
        systemProperty(
            "theta.canary.dist",
            layout.buildDirectory.dir("distributions/Theta-svcomp").get().asFile.absolutePath,
        )
        systemProperty("theta.canary.mode", (project.findProperty("theta.canary.mode") ?: "parse").toString())
        // The sweep runs PARALLEL_JOBS tasks at once (script default 4). Lowering it trades wall
        // time for memory headroom on a shared machine. The largest canaries need several GB each,
        // so this is pressure relief, not a substitute for enough memory.
        (project.findProperty("theta.canary.jobs"))?.let { environment("PARALLEL_JOBS", it.toString()) }
        (project.findProperty("theta.canary.svBenchmarks"))?.let {
            systemProperty("theta.canary.svBenchmarks", it.toString())
        }

        // The result depends on the benchmarks and the built archive, not only on this project's
        // inputs, so caching a green run would hide a regression in either.
        outputs.upToDateWhen { false }

        testLogging {
            events("failed", "skipped")
            showStandardStreams = false
        }
    }

// Keep the long sweep out of the ordinary test task.
tasks.named<Test>("test") { filter { excludeTestsMatching("*CanarySuiteTest*") } }
