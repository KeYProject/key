import java.util.*


plugins {
    java
    `java-library`
    `maven-publish`
    signing // GPG siging of artifacts, required by maven central
    idea
    eclipse
    checkstyle
    pmd

    // Code formatting
    id("com.diffplug.spotless") version "6.25.0"

    // EISOP Checker Framework
    id("org.checkerframework") version "0.6.48"
}

group = rootProject.group
version = rootProject.version

repositories {
    mavenCentral()
}

val implementation by configurations
dependencies {
    implementation(libs.slf4j)

    compileOnly(libs.jspecify)
    testCompileOnly(libs.jspecify)

    compileOnly(libs.eisopCheckerQual)
    compileOnly(libs.eisopUtil)
    testCompileOnly(libs.eisopCheckerQual)
    checkerFramework(libs.eisopCheckerQual)
    checkerFramework(libs.eisopChecker)

    testImplementation(libs.bundles.testing)
    testImplementation(project(":key.util"))
    testRuntimeOnly(libs.junitEngine)
}

java {
    sourceCompatibility = JavaVersion.VERSION_21
    targetCompatibility = JavaVersion.VERSION_21
}


tasks.withType<JavaCompile>().configureEach {
    options.encoding = "UTF-8"
    options.release.set(21)
}

tasks.withType<Javadoc>().configureEach {
    isFailOnError = false
    options.addBooleanOption("Xdoclint:none", true)
    options.encoding = "UTF-8"
    options.addBooleanOption("html5", true)
}

tasks.withType<Test>().configureEach {
    systemProperty("test-resources", "src/test/resources")
    systemProperty("testcases", "src/test/resources/testcase")
    systemProperty("TACLET_PROOFS", "tacletProofs")
    systemProperty("EXAMPLES_DIR", file("${rootProject.projectDir}/key.ui/examples"))
    systemProperty("RUNALLPROOFS_DIR", "$buildDir/report/runallproves")

    systemProperty("key.disregardSettings", "true")
    maxHeapSize = "4g"

    forkEvery = 0
    maxParallelForks = 1
}

tasks.withType<Test>().configureEach {
    useJUnitPlatform {
        includeEngines("junit-jupiter")
    }
}

tasks.named<Test>("test") {
    // Before we switched to JUnit 5, we used JUnit 4 with a customized discovery of test class.
    // This discovery called AutoSuite and searched in the compiled classes. AutoSuite was
    // necessary due to bugs caused in some execution order.
    // AutoSuites made the test order deterministic. A last known commit to find AutoSuite (for the case),
    // is 980294d04008f6b3798986bce218bac2753b4783.

    useJUnitPlatform {
        excludeTags("owntest", "interactive", "performance")
    }

    afterTest { desc, result ->
        logger.error("${result.resultType}: ${desc.className}#${desc.name}")
    }
    beforeTest { desc ->
        logger.error("> ${desc.className}#${desc.name}")
    }

    testLogging {
        outputs.upToDateWhen { false }
        showStandardStreams = true
    }
}

tasks.register<Test>("testFast") {
    group = "verification"
    useJUnitPlatform {
        excludeTags("slow", "performance", "interactive")
    }

    testLogging {
        // set options for log level LIFECYCLE
        events("failed")
        exceptionFormat = TestExceptionFormat.SHORT

        // set options for log level DEBUG
        debug {
            events("started", "skipped", "failed")
            exceptionFormat = TestExceptionFormat.FULL
        }

        info {
            // remove standard output/error logging from --info builds
            // by assigning only 'failed' and 'skipped' events
            events("failed", "skipped")
        }
    }
}

// The following two tasks can be used to execute main methods from the project
// The main class is set via "gradle -DmainClass=... execute --args ..."
// see https://stackoverflow.com/questions/21358466/gradle-to-execute-java-class-without-modifying-build-gradle
tasks.register<JavaExec>("execute") {
    description = "Execute main method from the project. Set main class via 'gradle -DmainClass=... execute --args ...'"
    group = "application"
    mainClass.set(System.getProperty("mainClass"))
    classpath = sourceSets.main.get().runtimeClasspath
}

tasks.register<JavaExec>("executeInTests") {
    description =
        "Execute main method from the project (tests loaded). Set main class via 'gradle -DmainClass=... execute --args ...'"
    group = "application"
    mainClass.set(System.getProperty("mainClass"))
    classpath = sourceSets.test.get().runtimeClasspath
}

pmd {
    isIgnoreFailures = true
    toolVersion = "6.53.0"
    consoleOutput = false
    ruleSets = listOf("category/java/errorprone.xml", "category/java/bestpractices.xml")
}

tasks.register<Pmd>("pmdMainChanged") {
    val changedFiles = getChangedFiles()
    source = files(pmdMain.source.filter { it.absolutePath in changedFiles })
    classpath = checkstyleMain.classpath
    reports {
        html.required.set(true)
        html.outputLocation.set(file("build/reports/pmd/main_diff.html"))
        xml.required.set(true)
        xml.outputLocation.set(file("build/reports/pmd/main_diff.xml"))
    }
}

checkstyle {
    toolVersion = "10.6.0"
    isIgnoreFailures = true
    configFile = file("$rootDir/gradle/key_checks.xml")
    showViolations = false // disable console output
}

tasks.register<Checkstyle>("checkstyleMainChanged") {
    val changedFiles = getChangedFiles()
    source = files(checkstyleMain.source.filter { it.absolutePath in changedFiles })
    classpath = checkstyleMain.classpath
    reports {
        html.required.set(true)
        html.outputLocation.set(file("build/reports/checkstyle/main_diff.html"))
        xml.required.set(true)
        xml.outputLocation.set(file("build/reports/checkstyle/main_diff.xml"))
    }
}

tasks.withType<Pmd>().configureEach {
    reports {
        xml.required.set(true)
        html.required.set(true)
    }
}

tasks.register<Jar>("sourcesJar") {
    description = "Create a jar file with the sources from this project"
    from(sourceSets.main.get().allJava)
    archiveClassifier.set("sources")
}

tasks.register<Jar>("javadocJar") {
    description = "Create a jar file with the javadocs from this project"
    from(tasks.javadoc)
    archiveClassifier.set("javadoc")
}

license {
    header = file("$rootDir/gradle/header")
    mapping {
        java = "SLASHSTAR_STYLE"
        javascript = "SLASHSTAR_STYLE"
    }
    mapping("key", "SLASHSTAR_STYLE")
}

eclipse {
    classpath {
        file {
            whenMerged {
                entries.findAll { it.path.endsWith("src/test/antlr") }.forEach { it.excludes = listOf("**/*.java") }
                entries.findAll { it.path.endsWith("/resources") }.forEach { it.excludes = listOf("**/*.java") }
            }
        }
    }
}

spotless {
    format("Key") {
        target("src/main/resources/**/*.key")
        trimTrailingWhitespace()
        endWithNewline()
    }

    antlr4 {
        target("src/*/antlr4/**/*.g4")
    }

    java {
        targetExclude("build/**")
        toggleOffOn()
        removeUnusedImports()
        eclipse().configFile("$rootDir/scripts/tools/checkstyle/keyCodeStyle.xml")
        trimTrailingWhitespace()
        importOrder("java|javax", "de.uka", "org.key_project", "", "\\#")
        if (project.name == "recoder") {
            licenseHeaderFile("$rootDir/gradle/header-recoder", "(package|import|//)")
        } else {
            licenseHeaderFile("$rootDir/gradle/header", "(package|import|//)")
        }
    }
}

afterEvaluate {
    publishing {
        publications {
            create<MavenPublication>("mavenJava") {
                from(components["java"])
                artifact(tasks["sourcesJar"])
                artifact(tasks["javadocJar"])
                pom {
                    name.set(project.name)
                    description.set(project.description)
                    url.set("https://key-project.org/")
                    licenses {
                        license {
                            name.set("GNU General Public License (GPL), Version 2")
                            url.set("https://www.gnu.org/licenses/old-licenses/gpl-2.0.html")
                        }
                    }
                    developers {
                        developer {
                            id.set("key")
                            name.set("KeY Developers")
                            email.set("support@key-project.org")
                            url.set("https://www.key-project.org/about/people/")
                        }
                    }
                    scm {
                        connection.set("scm:git:git://github.com/keyproject/key.git")
                        developerConnection.set("scm:git:git://github.com/keyproject/key.git")
                        url.set("https://github.com/keyproject/key/")
                    }
                }
            }
        }
        repositories {
            maven {
                if (project.version.toString().endsWith("-SNAPSHOT")) {
                    name = "mavenSnapshot"
                    url = uri("https://s01.oss.sonatype.org/content/repositories/snapshots/")
                    credentials {
                        username = project.findProperty("ossrhUsername") as String? ?: ""
                        password = project.findProperty("ossrhPassword") as String? ?: ""
                    }
                } else {
                    name = "mavenStaging"
                    url = uri("https://s01.oss.sonatype.org/service/local/staging/deploy/maven2/")
                    credentials {
                        username = project.findProperty("ossrhUsername") as String? ?: ""
                        password = project.findProperty("ossrhPassword") as String? ?: ""
                    }
                }
            }
        }
    }

    signing {
        useGpgCmd()
        sign(publishing.publications["mavenJava"])
    }
}

//conditionally enable jacoco coverage when `-DjacocoEnabled=true` is given on CLI.
val jacocoEnabled = System.properties.getProperty("jacocoEnabled") ?: "false"
if (jacocoEnabled.toBoolean()) {
    project.logger.lifecycle("Jacoco enabled. Test performance will be slower.")
    apply from : rootProject . file ("scripts/jacocokey.gradle")
}

val changedFiles by lazy {
    // Get the target and source branch
    val anchor = "git merge-base HEAD origin/main".execute().text.trim()

    // Get list of all changed files including status
    val allFiles = "git diff --name-status --diff-filter=dr $anchor".execute().text.trim().split("\n")

    // Remove the status prefix
    val files = TreeSet<String>()
    for (file in allFiles) {
        if (file.length > 1) {
            val a = file.substring(1).trim()
            if (a.isNotBlank()) {
                files.add("$rootDir/$a")
            }
        }
    }
    // Return the list of touched files
    files
}

fun String.execute(): Process {
    return Runtime.getRuntime().exec(this)
}
