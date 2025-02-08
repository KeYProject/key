plugins {
    id("java-convention")
}

description = "Generic data structures for terms and formulas without " +
        "dependencies to a specific target programming language"

dependencies {
    api(project(":key.util"))
}

val packages = "org\\.key_project\\.logic"
