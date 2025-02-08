plugins {
    id("java-convention")
}

description = "API for using KeY as a symbolic execution engine for Java programs"

dependencies {
    implementation(project(":key.core"))
    testImplementation(project(":key.core", configuration = "testArtifacts"))
}

tasks.test {
    maxHeapSize = "4g"
    systemProperty("UPDATE_TEST_ORACLE", System.getProperty("UPDATE_TEST_ORACLE"))
    systemProperty("ORACLE_DIRECTORY", System.getProperty("ORACLE_DIRECTORY"))
}
