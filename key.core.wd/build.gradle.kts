plugins {
    id("java-convention")
}

dependencies {
    api(project(":key.core"))
    testImplementation(testFixtures(project(":key.core")))
}

tasks.register<Test>("testRunAllWdProofs") {
    description = "Prove/reload all keyfiles tagged for regression testing"
    group = "verification"
    filter {
        includeTestsMatching ("RunAllProofsWd")
    }
}


val rapDir = layout.buildDirectory.dir("generated-src/rap/").get()
sourceSets["test"].java.srcDirs(rapDir)

tasks.register<JavaExec>("generateRAPUnitTests") {
    classpath = sourceSets["test"].runtimeClasspath
    mainClass.set("de.uka.ilkd.key.wd.GenerateUnitTests")
    args(rapDir)
}
