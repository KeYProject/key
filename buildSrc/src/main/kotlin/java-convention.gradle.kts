import org.gradle.api.tasks.testing.logging.TestExceptionFormat
import org.gradle.api.tasks.testing.logging.TestLogEvent
import org.gradle.plugins.ide.eclipse.model.Classpath
import org.gradle.plugins.ide.eclipse.model.SourceFolder

plugins {
    java
    `java-library`
    `maven-publish`
    signing       // GPG signing of artifacts, required by maven central
    idea
    eclipse

    id("com.diffplug.spotless")
    id("org.checkerframework")
}

//conditionally enable jacoco coverage when `-DjacocoEnabled=true` is given on CLI.
val jacocoEnabled = System.getProperty("jacocoEnabled", "false").toBoolean()
if (jacocoEnabled) {
    project.logger.lifecycle("Jacoco enabled. Test performance will be slower.")
}

java {
    toolchain {
        languageVersion = JavaLanguageVersion.of(21)
    }

    withJavadocJar()
    withSourcesJar()
}

repositories {
    mavenCentral()
    maven {
        url = uri("https://git.key-project.org/api/v4/projects/35/packages/maven")
    }
}

internal val Project.libs: VersionCatalog
    get() = project.extensions.getByType<VersionCatalogsExtension>().named("libs")

dependencies {
    implementation(libs.findLibrary("slf4j").get())
    api(libs.findLibrary("jspecify").get())

    compileOnly(libs.findLibrary("eisopCheckerQual").get())
    compileOnly(libs.findLibrary("eisopUtil").get())
    checkerFramework(libs.findLibrary("eisopCheckerQual").get())
    checkerFramework(libs.findLibrary("eisopUtil").get())

    // Testing
    testCompileOnly(libs.findLibrary("eisopCheckerQual").get())

    testImplementation(platform(libs.findLibrary("junit-bom").get()))
    testImplementation(libs.findBundle("testing").get())

    testRuntimeOnly(libs.findLibrary("junit.engine").get())
    testRuntimeOnly(libs.findLibrary("junit.platform").get())

    testImplementation(project(":key.util"))
}

tasks.withType<JavaCompile>().configureEach {
    // Setting UTF-8 as the java source encoding.
    options.encoding = "UTF-8"
}

tasks.withType<Javadoc>() {
    isFailOnError = false
    val o = options as CoreJavadocOptions
    o.addBooleanOption("Xdoclint:none", true)
    //options.verbose()
    o.encoding = "UTF-8"
    o.addBooleanOption("html5", true)
}

tasks.withType<Test>().configureEach {
    val examplesDir = rootProject.layout.projectDirectory.dir("key.ui/examples").getAsFile()
    val runAllProofsReportDir = layout.buildDirectory.dir("report/runallproves/").get().getAsFile()

    systemProperty("test-resources", "src/test/resources")
    systemProperty("testcases", "src/test/resources/testcase")
    systemProperty("TACLET_PROOFS", "tacletProofs")
    systemProperty("EXAMPLES_DIR", "$examplesDir")
    systemProperty("RUNALLPROOFS_DIR", "$runAllProofsReportDir")
    systemProperty("key.disregardSettings", "true")

    maxHeapSize = "4g"

    forkEvery = 0 //default
    maxParallelForks = 1 // weigl: test on master

    useJUnitPlatform {
        includeEngines("junit-jupiter")
    }

    // these seems to be missing starting with Gradle 9
    testClassesDirs = sourceSets["test"].output.classesDirs
    classpath = sourceSets["test"].runtimeClasspath

    // Fail on empty test suites
    addTestListener(object : TestListener {
        override fun beforeSuite(suite: TestDescriptor) {}
        override fun beforeTest(testDescriptor: TestDescriptor) {}
        override fun afterTest(testDescriptor: TestDescriptor, result: TestResult) {}
        override fun afterSuite(suite: TestDescriptor, result: TestResult) {
            require(result.testCount > 0) {
                "There are no executed test. This is unexpected and should be investigated!"
            }
        }
    })
}

tasks.test {
    // Before we switched to JUnit 5, we used JUnit 4 with a customized discovery of test class.
    // This discovery called AutoSuite and searched in the compiled classes. AutoSuite was
    // necessary due to bugs caused in some execution order.
    // AutoSuites made the test order deterministic. A last known commit to find AutoSuite (for the case),
    // is 980294d04008f6b3798986bce218bac2753b4783.

    useJUnitPlatform {
        excludeTags("owntest", "interactive", "performance")
    }

    testLogging {
        outputs.upToDateWhen { false }
        showStandardStreams = false

        // set options for log level LIFECYCLE
        events = setOf(TestLogEvent.FAILED)
        exceptionFormat = TestExceptionFormat.SHORT

        // set options for log level DEBUG
        info {
            // remove standard output/error logging from --info builds
            // by assigning only 'failed' and 'skipped' events
            events = setOf(TestLogEvent.FAILED, TestLogEvent.SKIPPED)
            exceptionFormat = TestExceptionFormat.SHORT
            showStandardStreams = true
            showStackTraces = true
        }

        // set options for log level DEBUG
        debug {
            events = setOf(
                TestLogEvent.STARTED, TestLogEvent.SKIPPED, TestLogEvent.FAILED, TestLogEvent.PASSED
            )
            exceptionFormat = TestExceptionFormat.FULL
            showStackTraces = true
            showStandardStreams = true
        }
    }
}


// The following two tasks can be used to execute main methods from the project
// The main class is set via "gradle -DmainClass=... execute --args ..."
// see https://stackoverflow.com/questions/21358466/gradle-to-execute-java-class-without-modifying-build-gradle
tasks.register<JavaExec>("execute") {
    description =
        "Execute main method from the project. Set main class via \"gradle -DmainClass=... execute --args ...\""
    group = "application"
    mainClass.set(System.getProperty("mainClass"))
    classpath = sourceSets["main"].runtimeClasspath
}

tasks.register<JavaExec>("executeInTests") {
    description =
        "Execute main method from the project (tests loaded). Set main class via \"gradle -DmainClass=... execute --args ...\""
    group = "application"
    mainClass.set(System.getProperty("mainClass"))
    classpath = sourceSets["test"].runtimeClasspath
}

eclipse.classpath.file {
    whenMerged(Action<Classpath> { ->
        // This adds the exclude entry for every resource and antlr folder.
        //As eclipse is so stupid, that it does not distuinguish between resource and java folder correctly.
        entries.filterIsInstance<SourceFolder>().filter { it -> it.path.endsWith("src/test/antlr") }
            .forEach { it.excludes = listOf("**/*.java") }

        entries.filterIsInstance<SourceFolder>().filter { it.path.endsWith("/resources") }
            .forEach { it.excludes = listOf("**/*.java") }
    })
}

spotless {
    // see https://github.com/diffplug/spotless/tree/main/plugin-gradle

    // optional: limit format enforcement to just the files changed by this feature branch
    // ratchetFrom 'origin/master'

    format("Key") {
        // define the files to apply `misc` to
        //target '*.gradle', '*.md', '.gitignore'
        target("src/main/resources/**/*.key")
        trimTrailingWhitespace()
        //indentWithSpaces(4)       // this does not really work
        endWithNewline()
        // TODO: license headers are problematic at the moment,
        //  see https://git.key-project.org/key/key/-/wikis/KaKeY%202022-09-30
        //licenseHeaderFile("$rootDir/gradle/header", '\\s*\\\\\\w+')
    }

    antlr4 {
        target("src/*/antlr4/**/*.g4") // default value, you can change if you want
        //licenseHeaderFile "$rootDir/gradle/header"
    }

    java {
        //target("*.java")
        // don't need to set target, it is inferred from java

        // We ignore the build folder to avoid double checks and checks of generated code.
        targetExclude("build/**")

        // allows us to use spotless:off / spotless:on to keep pre-formatted sections
        // MU: Only ... because of the eclipse(...) below, it is "@formatter:off" and "@formatter:on"
            // that must be used instead.
            toggleOffOn()

            removeUnusedImports()

            /* When new options are added in new versions of the Eclipse formatter, the easiest way is to export the new
             * style file from the Eclipse GUI and then use the CodeStyleMerger tool in
             * "$rootDir/scripts/tools/checkstyle/CodeStyleMerger.java" to merge the old and the new style files,
             * i.e. "java CodeStyleMerger.java <oldStyleFile> <newStyleFile> keyCodeStyle.xml". The tool adds all
             * entries with keys that were not present in the old file and optionally overwrites the old entries. The
             * file is output with ordered keys, such that the file can easily be diffed using git.
             */
            eclipse().configFile("$rootDir/scripts/tools/checkstyle/keyCodeStyle.xml")
            trimTrailingWhitespace()        // not sure how to set this in the xml file ...
            //googleJavaFormat().aosp().reflowLongStrings()

            // note: you can use an empty string for all the imports you didn't specify explicitly,
            // '|' to join group without blank line, and '\\#` prefix for static imports
            importOrder("java|javax", "de.uka", "org.key_project", "", "\\#")

            // specific delimiter: normally just 'package', but spotless crashes for files in default package
            // (see https://github.com/diffplug/spotless/issues/30), therefore 'import' is needed. '//' is for files
            // with completely commented out code (which would probably better just be removed in future).
            if (project.name == "recoder") {
                licenseHeaderFile("$rootDir/gradle/header-recoder", "(package|import|//)")
            } else {
                licenseHeaderFile("$rootDir/gradle/header", "(package|import|//)")
            }
        }
}

publishing {
    publications {
        create<MavenPublication>("mavenJava") {
            from(components["java"])
            pom {
                name = project.name
                description = project.description
                url = "https://key-project.org/"

                licenses {
                    license {
                        name = "GNU General Public License (GPL), Version 2"
                        url = "https://www.gnu.org/licenses/old-licenses/gpl-2.0.html"
                    }
                }

                developers {
                    developer {
                        id = "key"
                        name = "KeY Developers"
                        email = "support@key-project.org"
                        url = "https://www.key-project.org/about/people/"
                    }
                }
                scm {
                    connection = "scm:git:git://github.com/keyproject/key.git"
                    developerConnection = "scm:git:git://github.com/keyproject/key.git"
                    url = "https://github.com/keyproject/key/"
                }
            }
        }
    }
    repositories {
        maven {
            name = "Maven Central"
            /**
             * To be able to publish things on Maven Central, you need two things:
             *
             * (1) a JIRA account with permission on group-id `org.key-project`
             * (2) a keyserver-published GPG (w/o sub-keys)
             *
             * Your `$HOME/.gradle/gradle.properties` should like this:
             * ```
             * signing.keyId=YourKeyId
             * signing.password=YourPublicKeyPassword
             * ossrhUsername=your-jira-id
             * ossrhPassword=your-jira-password
             * ```
             *
             * You can test signing with `gradle sign`, and publish with `gradle publish`.
             * https://central.sonatype.org/publish/publish-guide/
             */
            val ossrhUsername = project.properties.getOrDefault("ossrhUsername", "").toString()
            val ossrhPassword = project.properties.getOrDefault("ossrhPassword", "").toString()

            if (project.version.toString().endsWith("-SNAPSHOT")) {
                name = "mavenSnapshot"
                url = uri("https://s01.oss.sonatype.org/content/repositories/snapshots/")
                credentials {
                    username = ossrhUsername
                    password = ossrhPassword
                }
            } else {
                name = "mavenStaging"
                url = uri("https://s01.oss.sonatype.org/service/local/staging/deploy/maven2/")
                credentials {
                    username = ossrhUsername
                    password = ossrhPassword
                }
            }
        }

        maven {
            // deployment to git.key-project.org
            name = "Keylab"
            url = uri("https://git.key-project.org/api/v4/projects/35/packages/maven")
            credentials(HttpHeaderCredentials::class) {
                if (System.getenv("TOKEN") != null) {
                    name = "Private-Token" // for private pushing
                    value = findProperty("keylab.token") as String?
                            ?: System.getenv("keylab.token").toString()
                } else {
                    name = "Job-Token"  // for gitlab CI
                    value = System.getenv("CI_JOB_TOKEN")
                }
            }
            authentication {
                create("header", HttpHeaderAuthentication::class)
            }
        }
    }
}

signing {
    useGpgCmd() // works better than the Java implementation, which requires PGP keyrings.
    sign(publishing.publications.getByName("mavenJava"))
}


val CHECKER_FRAMEWORK_PACKAGES_REGEX: String? by project
extra["CHECKER_FRAMEWORK_PACKAGES_REGEX"] = "^org\\.key_project"

checkerFramework {
    if(System.getProperty("ENABLE_NULLNESS").toBoolean()) {
        checkers = listOf("org.checkerframework.checker.nullness.NullnessChecker")
        extraJavacArgs = listOf(
            CHECKER_FRAMEWORK_PACKAGES_REGEX?.let { "-AonlyDefs=$it" }
                ?: "",
            "-Xmaxerrs", "10000",
            "-Astubs=$projectDir/src/main/checkerframework:permit-nullness-assertion-exception.astub:checker.jar/junit-assertions.astub",
            "-AstubNoWarnIfNotFound",
            "-Werror",
            "-Aversion",
        )
    }
}
