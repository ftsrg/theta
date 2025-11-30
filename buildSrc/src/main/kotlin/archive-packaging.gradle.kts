/*
 *  Archive packaging plugin
 *  Makes it possible for any subproject to declare zero or more tool variants to package.
 *  Subprojects configure:
 *    archivePackaging {
 *       variant {
 *          toolName = "Theta"
 *          portfolio = "STABLE"          // inserted into README as INPUT_FLAG
 *          scriptName = "theta-start.sh"  // copied from scripts/ directory (or custom path)
 *          solvers = listOf("cvc5:1.2.0", ...)
 *          includeSolverCli = true        // optional
 *       }
 *       variant { ... }
 *    }
 */

import org.gradle.api.tasks.bundling.Zip
import org.gradle.kotlin.dsl.create
import org.gradle.kotlin.dsl.register

open class ArchivePackagingVariant {
	var toolName: String = ""
	var portfolio: String = ""
	var scriptName: String = "theta-start.sh"
	var solvers: List<String> = emptyList()
	var includeSolverCli: Boolean = true
	var readmeTemplate: File? = null            // optional override
	var scriptSource: File? = null              // optional override
	var taskName: String? = null                // custom task name (else buildArchive<toolName> or buildArchive)
	var smoketestSource: File? = null           // optional smoketest path (omit if null/missing)
	var inputSource: File? = null               // optional input.c path (omit if null/missing)
}

open class ArchivePackagingExtension {
	internal val variants: MutableList<ArchivePackagingVariant> = mutableListOf()
	fun variant(configure: ArchivePackagingVariant.() -> Unit) {
		variants += ArchivePackagingVariant().apply(configure)
	}
}

val packagingExt = extensions.create<ArchivePackagingExtension>("archivePackaging")

// Utility to obtain current commit hash
fun commitHash(): String = try {
	val p = ProcessBuilder("git", "rev-parse", "HEAD")
		.redirectOutput(ProcessBuilder.Redirect.PIPE)
		.redirectError(ProcessBuilder.Redirect.PIPE)
		.start()
	p.waitFor()
	p.inputStream.bufferedReader().readText().trim().ifBlank { "unknown" }
} catch (_: Exception) { "unknown" }

afterEvaluate {
	if (packagingExt.variants.isEmpty()) return@afterEvaluate

	val downloadLibs = rootProject.tasks.findByName("downloadJavaSmtLibs")
	val mainShadow = tasks.findByName("shadowJar")
	if (mainShadow == null) {
		logger.warn("archive-packaging: shadowJar task missing in ${project.path}, skipping variant task registration")
		return@afterEvaluate
	}
	val solverCliShadow = if (packagingExt.variants.any { it.includeSolverCli }) {
		rootProject.projectOrNull(":theta-solver-smtlib-cli")?.tasks?.findByName("shadowJar")
	} else null

	// Default resource files removed: only explicitly configured files are included.
	val defaultScriptDir = rootProject.file("scripts")

	packagingExt.variants.forEachIndexed { idx, v ->
		require(v.toolName.isNotBlank()) { "archivePackaging variant toolName must be set" }
		val taskName = v.taskName ?: run {
			if (v.toolName == "Theta") "buildArchive" else "buildArchive${v.toolName}"
		}
		val existing = tasks.findByName(taskName)
		val reg = if (existing != null && existing is Zip) {
			existing as Zip
		} else if (existing != null) {
			logger.warn("archive-packaging: task $taskName exists but is not Zip, skipping configuration")
			return@forEachIndexed
		} else {
			tasks.register<Zip>(taskName).get()
		}

		(reg as Zip).apply {
			group = "distribution"
			description = "Create ${v.toolName} SV-COMP binary archive"

			// Dependencies
			if (downloadLibs != null) dependsOn(downloadLibs)
			dependsOn(mainShadow)
			if (v.includeSolverCli && solverCliShadow != null) dependsOn(solverCliShadow)
			archiveFileName.set("${v.toolName}-archive.zip")
			destinationDirectory.set(layout.buildDirectory.dir("distributions"))

			val commit = commitHash()
			val versionStr = project.version.toString()
			val scriptSourceFile = v.scriptSource ?: defaultScriptDir.resolve(v.scriptName)
			val readmeTemplate = v.readmeTemplate
			val smoketestFile = v.smoketestSource
			val inputCFile = v.inputSource

			into(v.toolName) {
				// native libs
				from(rootProject.file("lib")) { into("lib") }
				// license/meta
				from(rootProject.file("CONTRIBUTORS.md"))
				from(rootProject.file("LICENSE"))
				from(rootProject.file("lib/README.md")) { rename { "LIB_LICENSES.md" } }
				from(rootProject.file("README.md")) { rename { "GENERAL_README.md" } }
				// script
				if (scriptSourceFile.exists()) {
					from(scriptSourceFile) { rename { v.scriptName } }
				} else {
					logger.warn("archive-packaging: script ${scriptSourceFile.path} not found for ${v.toolName}")
				}
				// templated README (include only if explicitly set and exists)
				if (readmeTemplate != null && readmeTemplate.exists()) {
					from(readmeTemplate) {
						filter { line ->
							line.replace("TOOL_NAME", v.toolName)
								.replace("INPUT_FLAG", "--portfolio ${v.portfolio}")
								.replace("SCRIPTNAME", v.scriptName)
								.replace("COMMIT_ID", commit)
						}
						rename { "README.md" }
					}
				}
				// smoketest + input (include only if explicitly set and exists)
				if (smoketestFile != null && smoketestFile.exists()) from(smoketestFile)
				if (inputCFile != null && inputCFile.exists()) from(inputCFile)
				// main jar
				from(mainShadow) { rename { "theta.jar" } }
				// solver cli jar
				if (v.includeSolverCli && solverCliShadow != null) {
					from(solverCliShadow) { rename { "theta-smtlib.jar" } }
				}
				// empty solvers dir
				from(layout.buildDirectory.dir("empty-solvers")) { into("solvers") }
			}

			doFirst { layout.buildDirectory.dir("empty-solvers").get().asFile.mkdirs() }
		}
	}
}

// Helper to safely access project if it exists (rootProject.project() throws if missing)
fun Project.projectOrNull(path: String): Project? = try { rootProject.project(path) } catch (_: Exception) { null }

