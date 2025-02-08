import java.nio.file.Paths
import kotlin.io.path.readLines

plugins {
    id("java-convention")
    application
    // Used to create a single executable jar file with all dependencies
    // see task "shadowJar" below
    // https://github.com/GradleUp/shadow
    id("com.gradleup.shadow")
}

description = "User interface for the deductive verification of Java programs"

dependencies {
    implementation(project(":key.core"))
    implementation(project(":key.core.rifl"))

    implementation("com.formdev:flatlaf:3.6.1")

    implementation(project(":key.core.proof_references"))
    implementation(project(":key.core.symbolic_execution"))
    implementation(project(":key.removegenerics"))

    api(libs.miglayout)

    //logging implementation used by the slf4j
    implementation(libs.logback)

    api(libs.dockingFramesCommon)
    api(libs.dockingFramesCore)

    runtimeOnly(project(":keyext.ui.testgen"))
    runtimeOnly(project(":keyext.caching"))
    runtimeOnly(project(":keyext.exploration"))
    runtimeOnly(project(":keyext.slicing"))
    runtimeOnly(project(":keyext.proofmanagement"))
    runtimeOnly(project(":keyext.isabelletranslation"))
}

val createExamplesZip by tasks.registering(Zip::class) {
    description = "Create \"examples.zip\" containing all KeY examples"
    destinationDirectory = layout.buildDirectory.dir("resources/main/").getOrNull()
    archiveFileName = "examples.zip"
    from("examples")
    include(scanReadmeFiles()) // see end of file
}

tasks.processResources.get().dependsOn(createExamplesZip)

tasks.shadowJar {
    archiveClassifier.set("exe")
    archiveBaseName.set("key")
    mergeServiceFiles()
}

tasks.distZip {
    archiveBaseName.set("key")
}

application {
    mainClass.set("de.uka.ilkd.key.core.Main")
}

tasks.run {
    systemProperties["key.examples.dir"] = "$projectDir/examples"
    //systemProperties["slf4j.detectLoggerNameMismatch"] = true
    //systemProperties["KeyDebugFlag"] = "on"
    //args "--experimental"

    // this can be used to solve a problem where the OS hangs during debugging of popup menus
    // (see https://docs.oracle.com/javase/10/troubleshoot/awt.htm#JSTGD425)
    jvmArgs.add("-Dsun.awt.disablegrab=true")
}

tasks.register<JavaExec>("runWithProfiler") {
    group = "application"
    description = """Run key.ui with flight recoder enabled. 
                   See https://www.baeldung.com/java-flight-recorder-monitoring for a how to."""

    classpath = sourceSets["main"].runtimeClasspath
    mainClass.set("de.uka.ilkd.key.core.Main")
    jvmArgs = listOf(
        "-XX:+FlightRecorder",
        "-XX:StartFlightRecording=duration=30s,filename=key_profile.jfr",
        "-XX:FlightRecorderOptions=stackdepth=256"
    )
    doLast {
        println("A file key_profile.jfr has been created in folder 'key.ui' by JRE (FlightRecoder).")
        println("You can open key_profile.jfr in IntelliJ to inspect the performance measurement.")
    }
}

/**
 * Go and scan all registered README.txt files for files that need to be
 * included into examples.zip. Thus only those files that can actually be
 * accessed from the example browser are added to examples.zip.
 *
 * The file size is reduced considerably.
 *
 * @return a list of filenames to be added to examples.zip. Each line
 * is relative to the examples directory.
 */
fun scanReadmeFiles(): List<String> {
    val REGEX_FILE = "file".toRegex(RegexOption.IGNORE_CASE)
    val REGEX_EQ = "=".toRegex()

    val exampleDir = projectDir.toPath().resolve("examples")
    val examplesIndex = exampleDir.resolve("index").resolve("samplesIndex.txt")

    val result = mutableListOf("index/samplesIndex.txt")

    for (line in examplesIndex.readLines()) {
        val line = line.trim()
        if (line.isEmpty() || line.startsWith("#")) {
            continue
        }
        val entry = Paths.get(line.replace("/", File.separator))
        val readme = exampleDir.resolve(entry)
        val dir = entry.parent
        result.add(line)

        // The project file is not always project.key, but better include the default file.
        result.add("$dir/project.key")

        for (rmLine in readme.readLines()) {
            if (rmLine.startsWith("#") || "=" !in rmLine) continue
            val (key, value) = rmLine.split(REGEX_EQ, 2)
            if (key.trim().contains(REGEX_FILE)) {
                val filename = value.trim()
                result.add("$dir/$filename")
            }
        }
    }
    return result
}
