package de.uka.ilkd.key.tcg

plugins {
    java
}

repositories {
    mavenCentral()
}

dependencies {
    testImplementation(platform("org.junit:junit-bom:5.13.2"))
    testImplementation("org.junit.jupiter:junit-jupiter-api")
    testRuntimeOnly("org.junit.jupiter:junit-jupiter-engine")
    testRuntimeOnly("org.junit.platform:junit-platform-launcher")

    testImplementation("org.objenesis:objenesis:3.3")
    testImplementation("org.hamcrest:hamcrest-core:2.2")
}

tasks.withType<Test> {
    useJUnitPlatform()
}
