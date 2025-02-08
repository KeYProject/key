import java.util.Date

plugins {
    //Support for IntelliJ IDEA
    //https://docs.gradle.org/current/userguide/idea_plugin.html
    id("idea")

    //Support for Eclipse
    //https://docs.gradle.org/current/userguide/eclipse_plugin.html
    id("eclipse")  //support for Eclipse

    // Gives `gradle dependencyUpdate` to show which dependency has a newer version
    // id "com.github.ben-manes.versions" version "0.39.0"

    // Code formatting
    id("com.diffplug.spotless")
}

// Configure this project for use inside IntelliJ:
idea {
    module {
        isDownloadJavadoc = false
        isDownloadSources = true
    }
}

// The $BUILD_NUMBER is an environment variable set by Jenkins.
val build = System.getenv("BUILD_NUMBER")?.let { "-$it" } ?: "-dev"

group = "org.key-project"
version = "2.12.4$build"

// Generation of a JavaDoc across sub projects.
val alldoc = tasks.register<Javadoc>("alldoc") {
    group = "documentation"
    description = "Generate a JavaDoc across sub projects"

    subprojects.forEach { subproject ->
        if (subproject.plugins.hasPlugin("java")) {
            val sourceSets = subproject.extensions.getByName("sourceSets") as SourceSetContainer
            val main = sourceSets.getByName("main")
            source(main.allJava)
            classpath += main.compileClasspath
        }
    }
    destinationDir = layout.buildDirectory.dir("docs/javadoc").get().asFile

    with(options as StandardJavadocDocletOptions) {
        //showFromPrivate()
        encoding = "UTF-8"
        addBooleanOption("Xdoclint:none", true)
        // overview = new File( projectDir, 'src/javadoc/package.html' )
        //stylesheetFile = new File( projectDir, 'src/javadoc/stylesheet.css' )
        windowTitle = "KeY API Documentation"
        docTitle = "KeY JavaDoc ($project.version) -- ${Date()}"
        bottom = "Copyright &copy; 2003-2023 <a href=\"http://key-project.org\">The KeY-Project</a>."
        isUse=true
        links = listOf("https://docs.oracle.com/en/java/javase/21/docs/api/", "https://www.antlr.org/api/Java/")
    }
}

// Creates a jar file with the javadoc over all sub projects.
tasks.register<Zip>("alldocJar") {
    dependsOn(alldoc.get())
    description = "Create a jar file with the javadoc over all sub projects"
    from(alldoc.get())
    archiveFileName = "key-api-doc-${project.version}.zip"
    destinationDirectory = layout.buildDirectory.dir("distribution").get()
}
