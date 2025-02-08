plugins {
    id("java-convention")
}

description = "Proof exploration capabilities for key.ui"

dependencies {
    implementation( project(":key.core"))
    implementation (project(":key.ui"))
}