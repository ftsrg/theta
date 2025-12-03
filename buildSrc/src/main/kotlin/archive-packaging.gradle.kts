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
import java.io.Serializable

open class ArchivePackagingVariant : Serializable {
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

afterEvaluate {
	if (packagingExt.variants.isEmpty()) return@afterEvaluate

	// Capture everything from rootProject at configuration time
	val rootProjectDir = rootProject.projectDir
	val defaultScriptDir = File(rootProjectDir, "scripts")
	val hasSolverCli = packagingExt.variants.any { it.includeSolverCli } && 
		rootProject.subprojects.any { it.path == ":theta-solver-smtlib-cli" }
	
	val downloadLibsProvider = rootProject.tasks.named("downloadJavaSmtLibs")
	val mainShadowProvider = tasks.named("shadowJar")

	packagingExt.variants.forEachIndexed { idx, v ->
		require(v.toolName.isNotBlank()) { "archivePackaging variant toolName must be set" }
		val taskName = v.taskName ?: run {
			if (v.toolName == "Theta") "buildArchive" else "buildArchive${v.toolName}"
		}
		
		// Copy variant properties to avoid capturing script objects
		val toolName = v.toolName
		val portfolio = v.portfolio
		val scriptName = v.scriptName
		val solvers = v.solvers.toList()
		val includeSolverCli = v.includeSolverCli
		val versionStr = project.version.toString()
		val scriptSourceFile = v.scriptSource ?: defaultScriptDir.resolve(v.scriptName)
		val readmeTemplate = v.readmeTemplate
		val smoketestFile = v.smoketestSource
		val inputCFile = v.inputSource
		
		// Capture layout directories at configuration time
		val buildDirProvider = layout.buildDirectory
		val distributionsDir = buildDirProvider.dir("distributions")
		val solversDirPath = buildDirProvider.dir("solvers-$toolName")
		
		// Capture smtlib jar path if needed, without holding provider reference
		val smtlibJarPath = if (includeSolverCli && hasSolverCli) {
			// Resolve the task lazily via provider using Gradle API
			providers.provider {
				try {
					gradle.rootProject.tasks.findByPath(":theta-solver-smtlib-cli:shadowJar")?.let { task ->
						(task as org.gradle.jvm.tasks.Jar).archiveFile.get().asFile.absolutePath
					}
				} catch (e: Exception) {
					null
				}
			}
		} else {
			providers.provider { null }
		}
		
		// Create solver installation task if needed
		val installSolversTaskName = "installSolvers${toolName}"
		if (solvers.isNotEmpty()) {
			tasks.register(installSolversTaskName) {
				group = "distribution"
				description = "Install solvers for $toolName archive"
				
				// Depend on smtlib-cli jar
				if (includeSolverCli && hasSolverCli) {
					dependsOn(":theta-solver-smtlib-cli:shadowJar")
				}
				
				// Declare outputs
				outputs.dir(solversDirPath)
				
				doLast {
					val smtlibJar = smtlibJarPath.orNull
					if (smtlibJar == null) {
						println("archive-packaging: smtlib jar not available, skipping solver installation")
						return@doLast
					}
					
					val solversDir = solversDirPath.get().asFile
					solversDir.mkdirs()
					
					val smtlibJarFile = File(smtlibJar)
					if (!smtlibJarFile.exists()) {
						println("archive-packaging: ${smtlibJarFile.path} does not exist, skipping solver installation")
						return@doLast
					}
					
					solvers.forEach { solver ->
						println("Installing solver: $solver into ${solversDir.path}")
						try {
							val process = ProcessBuilder(
								"java", "-jar", smtlibJarFile.absolutePath,
								"--home", solversDir.absolutePath,
								"install", solver,
							).redirectErrorStream(true).start()
							
							val output = process.inputStream.bufferedReader().readText()
							val exitCode = process.waitFor()
							
							if (exitCode != 0) {
								println("Failed to install solver $solver (exit code: $exitCode)")
								println(output)
							} else {
								println("Successfully installed: $solver")
								if (output.isNotBlank()) {
									println(output)
								}
							}
						} catch (e: Exception) {
							println("Error installing solver $solver: ${e.message}")
						}
					}
				}
			}
		}
		
		// Use task provider instead of realizing task
		tasks.register<Zip>(taskName) {
			group = "distribution"
			description = "Create $toolName SV-COMP binary archive"

			// Dependencies using providers
			dependsOn(downloadLibsProvider)
			dependsOn(mainShadowProvider)
			if (includeSolverCli && hasSolverCli) {
				dependsOn(":theta-solver-smtlib-cli:shadowJar")
			}
			// Depend on solver installation task if it exists
			if (solvers.isNotEmpty()) {
				dependsOn(installSolversTaskName)
			}
			
			archiveFileName.set("$toolName-archive.zip")
			destinationDirectory.set(distributionsDir)
			
			into(toolName) {
				// native libs
				from(File(rootProjectDir, "lib")) { into("lib") }
				// license/meta
				from(File(rootProjectDir, "CONTRIBUTORS.md"))
				from(File(rootProjectDir, "LICENSE"))
				from(File(rootProjectDir, "lib/README.md")) { rename { "LIB_LICENSES.md" } }
				from(File(rootProjectDir, "README.md")) { rename { "GENERAL_README.md" } }
				// script
				if (scriptSourceFile.exists()) {
					from(scriptSourceFile) { 
						filter { line ->
							line.replace("TOOL_NAME", toolName)
								.replace("TOOL_VERSION", versionStr)
						}
						rename { scriptName }
						fileMode = 0b111101101 // 0755 in octal = rwxr-xr-x
					}
				} else {
					println("archive-packaging: script ${scriptSourceFile.path} not found for $toolName")
				}
				// templated README (include only if explicitly set and exists)
				if (readmeTemplate != null && readmeTemplate.exists()) {
					from(readmeTemplate) {
						filter { line ->
							line.replace("TOOL_NAME", toolName)
								.replace("INPUT_FLAG", "--portfolio $portfolio")
								.replace("SCRIPTNAME", scriptName)
								.replace("TOOL_VERSION", versionStr)
						}
						rename { "README.md" }
					}
				}
				// smoketest + input (include only if explicitly set and exists)
				if (smoketestFile != null && smoketestFile.exists()) from(smoketestFile)
				if (inputCFile != null && inputCFile.exists()) from(inputCFile)
				// main jar - use provider
				from(mainShadowProvider.map { (it as org.gradle.jvm.tasks.Jar).archiveFile }) { 
					rename { "theta.jar" } 
				}
				// solver cli jar - use provider
				if (includeSolverCli && hasSolverCli) {
					from(providers.provider {
						gradle.rootProject.tasks.findByPath(":theta-solver-smtlib-cli:shadowJar")?.let { task ->
							(task as org.gradle.jvm.tasks.Jar).archiveFile.get()
						}
					}) { 
						rename { "theta-smtlib.jar" } 
					}
				}
				// solvers directory - always include, will be empty or populated
        if (solvers.isNotEmpty()) {

          from(solversDirPath) {
            into("solvers")
          }

        }
			}
		}
	}
}