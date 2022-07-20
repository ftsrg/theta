object Deps {
    val guava = "com.google.guava:guava:${Versions.guava}"

    object Antlr {
        val antlr = "org.antlr:antlr4:${Versions.antlr}"
        val runtime = "org.antlr:antlr4-runtime:${Versions.antlr}"
    }

    val z3 = "lib/com.microsoft.z3.jar"

    val jcommander = "com.beust:jcommander:${Versions.jcommander}"

    val junit4 = "junit:junit:${Versions.junit}"

    object Mockito {
        val core = "org.mockito:mockito-core:${Versions.mockito}"
    }

    object Kotlin {
        val stdlib = "org.jetbrains.kotlin:kotlin-stdlib-jdk8:${Versions.kotlin}"
    }
}
