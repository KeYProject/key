import org.eclipse.jgit.lib.Repository
import org.eclipse.jgit.storage.file.FileRepositoryBuilder
import org.javacc.plugin.gradle.javacc.CompileJavaccTask
import java.nio.file.Files
import java.nio.file.StandardCopyOption

plugins {
    id("java-convention")
    id("org.javacc.javacc") version "4.0.1"
}

description = "Core functionality (terms, rules, prover, ...) for deductive verification of Java programs"

val antlr4 by configurations.creating


// region Exposing TEST artifact
// This is not good. Normally there is a Gradle way for exposing text fixtures.
// This is the lightweight variant to expose test classes to key.core.symbolic_execution.
// This dependency should be resolved in the future.
val testJar by tasks.registering(Jar::class) {
    archiveClassifier.set("test")
    from(sourceSets["test"].output)
}
artifacts {
    val testArtifacts by configurations.creating
    add("testArtifacts", testJar)
}
//endregion


dependencies {
    api(project(":key.util"))
    api(project(":key.ncore"))
    api(project(":key.ncore.calculus"))
    api(project(":recoder"))

    implementation(libs.javacc)
    javacc(libs.javacc)
    antlr4(libs.antlr)
    api(libs.antlrRuntime)
}

val javaCCOutputDir = layout.buildDirectory.dir("generated-src/javacc")
val javaCCOutputDirMain = javaCCOutputDir.map { it.dir("main") }

sourceSets["main"].java.srcDirs(
    javaCCOutputDirMain.get().asFile,
    file("$projectDir/build/generated-src/antlr4/main/")
)


tasks.named<CompileJavaccTask>("compileJavacc") {
    outputDirectory = javaCCOutputDirMain.get().asFile
    inputDirectory = file("src/main/javacc")
    doLast {
        // Some manual overwriting of Token files needed
        for (folder in listOf("schemajava", "proofjava")) {
            for (fil in listOf(
                "de/uka/ilkd/key/parser/$folder/Token.java",
                "de/uka/ilkd/key/parser/$folder/JavaCharStream.java"
            )) {
                Files.copy(
                    projectDir.toPath().resolve("src/main/javacc/$fil"),
                    javaCCOutputDirMain.get().asFile.toPath().resolve(fil),
                    StandardCopyOption.REPLACE_EXISTING
                )
            }
        }
    }
}

tasks.register("generateSMTListings") {
    val pack = "de/uka/ilkd/key/smt/newsmt2"
    val resourcesDir = file("src/main/resources")
    val outputDir = resourcesDir

    inputs.files(fileTree("$resourcesDir/$pack") {
        exclude("$resourcesDir/$pack/DefinedSymbolsHandler.preamble.xml")
    })
    outputs.file(file("$outputDir/$pack/DefinedSymbolsHandler.preamble.xml"))

    doLast {
        val outputFile = file("$outputDir/$pack/DefinedSymbolsHandler.preamble.xml")
        outputFile.bufferedWriter().use { writer ->
            writer.write(
                """
                <?xml version="1.0" encoding="UTF-8" standalone="no"?>
                <!DOCTYPE properties SYSTEM "http://java.sun.com/dtd/properties.dtd">
                <properties>
                """.trimIndent()
            )
            file("$resourcesDir/$pack").listFiles()?.forEach {
                if (it.name.endsWith(".DefinedSymbolsHandler.preamble.xml")) {
                    it.forEachLine { line -> writer.write(line) }
                }
            }
            writer.write("</properties>")
        }
    }
}

tasks.register("generateSolverPropsList") {
    val pack = "de/uka/ilkd/key/smt/solvertypes"
    val resourcesDir = file("src/main/resources")
    val outputDir = resourcesDir

    inputs.files(fileTree("$outputDir/$pack") {
        exclude("solvers.txt")
    })
    outputs.file(file("$outputDir/$pack/solvers.txt"))

    doLast {
        val list = mutableListOf<String>()
        file("$outputDir/$pack").walkTopDown().forEach {
            if (it.name.endsWith(".props")) list.add(it.name)
        }
        list.sort()
        file("$outputDir/$pack/solvers.txt").writeText(list.joinToString(System.lineSeparator()))
    }
}

tasks.named("classes") {
    dependsOn("generateSMTListings", "generateSolverPropsList")
}

tasks.register<Test>("testProveRules") {
    description = "Proves KeY taclet rules tagged as lemma"
    group = "verification"
    filter {
        includeTestsMatching("ProveRulesTest")
    }
}

tasks.register<Test>("testRunAllFunProofs") {
    description = "Prove/reload all keyfiles tagged for regression testing"
    group = "verification"
    filter {
        includeTestsMatching("RunAllProofsFunctional")
    }
}

tasks.register<Test>("testRunAllInfProofs") {
    description = "Prove/reload all keyfiles tagged for regression testing"
    group = "verification"
    filter {
        includeTestsMatching("RunAllProofsInfFlow")
    }
}

tasks.register<Test>("testProveSMTLemmas") {
    description = "Prove (or load proofs for) lemmas used in the SMT translation"
    group = "verification"
    filter {
        includeTestsMatching("ProveSMTLemmasTest")
    }
}

tasks.register<Test>("testStrictSMT") {
    description = "Run the tests for the new smt translation in strict mode"
    group = "verification"
    systemProperty("key.newsmt2.stricttests", "true")
    filter {
        includeTestsMatching("MasterHandlerTest")
    }
}


tasks.register("generateVersionFiles") {
    val outputFolder = file("build/resources/main/de/uka/ilkd/key/util")
    val sha1 = File(outputFolder, "sha1")
    val branch = File(outputFolder, "branch")
    val versionf = File(outputFolder, "version")

    inputs.file("${project.rootDir}/.git/HEAD")
    outputs.files(sha1, branch, versionf)

    doLast {
        val builder = FileRepositoryBuilder()
        val repository: Repository = builder.setGitDir(File(rootDir, ".git"))
            .readEnvironment()
            .findGitDir()
            .build()

        repository.use {
            val ref = it.resolve("HEAD")
            val version = ref?.name() ?: ""
            val short = ref?.abbreviate(8)?.name() ?: ""
            sha1.writeText(version)
            branch.writeText(short)
            versionf.writeText(rootProject.version.toString())
        }
    }
}

tasks.named("processResources") {
    dependsOn("generateVersionFiles", "generateSolverPropsList", "generateSMTListings")
}

val antlr4OutputKey = "$projectDir/build/generated-src/antlr4/main/de/uka/ilkd/key/nparser"

tasks.register<JavaExec>("runAntlr4Key") {
    inputs.files("src/main/antlr4/KeYLexer.g4", "src/main/antlr4/KeYParser.g4")
    outputs.dir(antlr4OutputKey)
    classpath = antlr4
    mainClass.set("org.antlr.v4.Tool")
    args = listOf(
        "-visitor", "-Xexact-output-dir", "-o", antlr4OutputKey,
        "-package", "de.uka.ilkd.key.nparser",
        "src/main/antlr4/KeYLexer.g4", "src/main/antlr4/KeYParser.g4"
    )
    doFirst {
        file(antlr4OutputKey).mkdirs()
        println("create $antlr4OutputKey")
    }
}

tasks.named("compileJava") {
    dependsOn("runAntlr4Key")
}

tasks.register<JavaExec>("debugKeyLexer") {
    mainClass.set("de.uka.ilkd.key.nparser.DebugKeyLexer")
    classpath = sourceSets["main"].runtimeClasspath
    standardInput = System.`in`
}

tasks.named("processResources") {
    dependsOn("generateVersionFiles")
}

val antlr4OutputJml = "$projectDir/build/generated-src/antlr4/main/de/uka/ilkd/key/speclang/njml"

tasks.register<JavaExec>("runAntlr4Jml") {
    inputs.files("src/main/antlr4/JmlLexer.g4", "src/main/antlr4/JmlParser.g4")
    outputs.dir(antlr4OutputJml)
    classpath = configurations["antlr4"]
    mainClass.set("org.antlr.v4.Tool")
    args = listOf(
        "-visitor",
        "-Xexact-output-dir", "-o", antlr4OutputJml,
        "-package", "de.uka.ilkd.key.speclang.njml",
        "src/main/antlr4/JmlLexer.g4", "src/main/antlr4/JmlParser.g4"
    )
    doFirst {
        file(antlr4OutputJml).mkdirs()
        println("create $antlr4OutputJml")
    }
}

tasks.named("compileJava") {
    dependsOn("runAntlr4Jml")
}

tasks.register<JavaExec>("debugJmlLexer") {
    mainClass.set("de.uka.ilkd.key.speclang.njml.DebugJmlLexer")
    classpath = sourceSets["main"].runtimeClasspath
    standardInput = System.`in`
}

tasks.register<Test>("ptest") {
    group = "verification"
}

val rapDir = layout.buildDirectory.dir("generated-src/rap")

tasks.register<JavaExec>("generateRAPUnitTests") {
    classpath = sourceSets["test"].runtimeClasspath
    mainClass.set("de.uka.ilkd.key.proof.runallproofs.GenerateUnitTests")
    args = listOf(rapDir.get().asFile.absolutePath)
}

sourceSets["test"].java.srcDirs(rapDir.get().asFile)

tasks.named("sourcesJar") {
    dependsOn("runAntlr4Jml", "runAntlr4Key", "compileJavacc")
}
