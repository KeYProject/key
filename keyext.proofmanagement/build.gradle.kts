plugins {
    id("java-convention")
    application
    id("com.gradleup.shadow")
}

description = "Management of larger verification with KeY."

dependencies {
    implementation(project(":key.core"))
    implementation(project(":key.ui"))

    implementation(libs.stringtemplate)
}

application {
    mainClass = "org.key_project.proofmanagement.Main"
    // for start script generated with createStartScripts
    applicationName = "pm"
}

tasks.run {
    // for debugging, something like this can be used:
    //args('check', '--missing', '--settings', '--report', 'proofManagementReport.html', '--replay', '--dependency', 'pmexample2')
    //args('merge', 'bundle1', 'bundle2.zip', 'output.zproof')

    // not necessary any more with the workaround in HTMLReport
    // needed for access of Node.getValue in string template
    // jvmArgs += ['--add-opens', 'java.base/java.util=ALL-UNNAMED']
}

tasks.shadowJar {
    archiveClassifier = "exe"
    archiveBaseName = "keyext.proofmanagement"
}
