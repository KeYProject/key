plugins {
    kotlin("jvm") version "1.9.0"
    id("org.openjfx.javafxplugin") version "0.0.14"
    id("org.javamodularity.moduleplugin") version "1.8.12"
    application
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(project(":key.core"))
    implementation(project(":key.core.rifl"))

    implementation(project(":key.core.proof_references"))
    implementation(project(":key.core.symbolic_execution"))
    implementation(project(":key.removegenerics"))

    implementation("ch.qos.logback:logback-classic:1.4.11")

    runtimeOnly(project(":keyext.ui.testgen"))
    runtimeOnly(project(":keyext.exploration"))
    runtimeOnly(project(":keyext.slicing"))
    runtimeOnly(project(":keyext.proofmanagement"))

    implementation(platform("org.jetbrains.kotlin:kotlin-bom"))
    implementation("no.tornado:tornadofx:1.7.20")
    implementation("org.fxmisc.richtext:richtextfx:0.11.1")
    implementation("org.kordamp.ikonli:ikonli-material2-pack:12.3.1")
    implementation("org.kordamp.ikonli:ikonli-fontawesome-pack:12.3.1")
    implementation("org.kordamp.ikonli:ikonli-javafx:12.3.1")
//    implementation("io.github.palexdev:materialfx:11.16.1")
    implementation("com.pixelduke:fxribbon:1.2.2")
    testImplementation(kotlin("test"))
}

tasks.test {
    useJUnitPlatform()
}

java {
    targetCompatibility = JavaVersion.VERSION_17
    sourceCompatibility = JavaVersion.VERSION_17
}

kotlin {
    jvmToolchain(17)
}

javafx {
    version = "20"
    modules("javafx.controls", "javafx.fxml")
}
