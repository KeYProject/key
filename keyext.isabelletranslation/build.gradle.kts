plugins {
    id("java-convention")
}

description = "Translation of Sequents to Isabelle"

dependencies {
    implementation(project(":key.core"))
    implementation(project(":key.ui"))
    implementation("de.unruh:scala-isabelle_2.13:0.4.3") {
        /*
        scala-isabelle uses slf4j-simple. As KeY is currently using logback, this would result in two slf4j providers.
        The code below excludes this module, thereby causing a fallback to logback.
         */
        exclude("org.slf4j:slf4j-simple")
    }
}

