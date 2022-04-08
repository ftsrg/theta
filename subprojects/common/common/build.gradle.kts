import java.io.ByteArrayOutputStream

plugins {
    id("java-common")
}

fun gitBranch(): String {
    return try {
        val byteOut = ByteArrayOutputStream()
        project.exec {
            commandLine = "git rev-parse --abbrev-ref HEAD".split(" ")
            standardOutput = byteOut
        }
        String(byteOut.toByteArray()).trim().also {
            if (it == "HEAD")
                logger.warn("Unable to determine current branch: Project is checked out with detached head!")
        }
    } catch (e: Exception) {
        logger.warn("Unable to determine current branch: ${e.message}")
        "Unknown Branch"
    }
}

fun gitHash(): String {
    return try {
        val byteOut = ByteArrayOutputStream()
        project.exec {
            commandLine = "git rev-parse HEAD".split(" ")
            standardOutput = byteOut
        }
        String(byteOut.toByteArray()).trim()
    } catch (e: Exception) {
        logger.warn("Unable to determine current commit: ${e.message}")
        "Unknown Commit"
    }
}

tasks {
    val projectProps by registering(WriteProperties::class) {
        description = "Write project version information to a file."

        outputFile = file("${buildDir}/version.properties")
        encoding = "UTF-8"
        comment = "Version and name of project"

        property("name", rootProject.name)
        property("version", rootProject.version)
        property("gitBranch", gitBranch())
        property("gitCommit", gitHash())
    }

    processResources {
        // Depend on output of the task to create properties,
        // so the properties file will be part of the Java resources.
        from(projectProps)
    }
}