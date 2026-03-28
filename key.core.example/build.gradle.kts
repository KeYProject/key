plugins {
    id("java-convention")
    application
}

description = "Example project to use KeY's APIs"

application {
    mainClass = "org.key_project.Main"
}

dependencies {
    implementation(project(":key.core"))
    implementation(libs.logback)
}