description = "Utility library of the key-project"

dependencies {
    implementation("org.jspecify:jspecify:1.0.0")
}

checkerFramework {
    if(System.getProperty("ENABLE_NULLNESS")) {
        checkers = [
                "org.checkerframework.checker.nullness.NullnessChecker",
        ]
        extraJavacArgs = [
                "-AonlyDefs=^org\\.key_project\\.util",
                "-Xmaxerrs", "10000",
                "-Astubs=$projectDir/src/main/checkerframework:permit-nullness-assertion-exception.astub:checker.jar/junit-assertions.astub",
                "-AstubNoWarnIfNotFound",
                "-Werror",
                "-Aversion",
        ]
    }
}
