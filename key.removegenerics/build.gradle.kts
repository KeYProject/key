plugins {
    id("java-convention")
    application
    id("com.gradleup.shadow")
}

description = "Helper to remove generics from Java source code"

dependencies {
    implementation (project(":key.core"))
}

application {
    mainClass.set("de.uka.ilkd.key.util.removegenerics.Main")
}

tasks.shadowJar {
    archiveClassifier = "exe"
    archiveBaseName = "key.removegenerics"
}
