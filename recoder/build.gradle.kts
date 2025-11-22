plugins {
    id("java-convention")
}

description = "Fork of the Recoder -- a parser/ast for Java with extensions for KeY-Java dialects."


dependencies {
    implementation (libs.bundles.recoder)
}