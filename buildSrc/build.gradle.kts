import org.gradle.kotlin.dsl.plugins

plugins {
    `kotlin-dsl`
    `kotlin-dsl-precompiled-script-plugins`
}

repositories {
    mavenCentral()
    gradlePluginPortal()
}

kotlin {
    jvmToolchain(21)
}

dependencies {
    implementation("com.diffplug.spotless:com.diffplug.spotless.gradle.plugin:7.2.1")
    implementation("org.checkerframework:org.checkerframework.gradle.plugin:0.6.56")
    implementation("com.gradleup.shadow:com.gradleup.shadow.gradle.plugin:9.0.2")

    implementation(libs.kotlinGradlePlugin)
}