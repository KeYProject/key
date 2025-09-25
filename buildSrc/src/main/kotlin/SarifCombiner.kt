import org.gradle.api.DefaultTask
import org.gradle.api.file.FileCollection
import org.gradle.api.file.RegularFileProperty
import org.gradle.api.provider.Property
import org.gradle.api.tasks.InputFiles
import org.gradle.api.tasks.OutputFile
import org.gradle.api.tasks.TaskAction
import org.jetbrains.kotlin.com.google.gson.Gson
import org.jetbrains.kotlin.com.google.gson.GsonBuilder
import org.jetbrains.kotlin.com.google.gson.JsonElement
import java.io.File

/**
 * Utility class for combining multiple SARIF (Static Analysis Results Interchange Format) files.
 *
 * This class provides a method to merge SARIF reports, which are commonly used for aggregating
 * static analysis results from different tools or runs into a single report.
 * 
 * The implementation has no deep understanding of the SARIF format and simply merges the `results` field.
 * Not applicable for multiple `run` or `tool` entries.
 *
 * @see <a href="https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html">SARIF Specification</a>
 */
/** */
private val JsonElement.getResultsOfFirstRun
    get() = asJsonObject.get("runs").asJsonArray.get(0).asJsonObject.get("results").asJsonArray

abstract class SarifJoiner : DefaultTask() {
    @get:InputFiles
    abstract val sarifFiles: Property<FileCollection>

    @get:OutputFile
    abstract val outputFile: RegularFileProperty

    @TaskAction
    fun run() {
        val inputs = sarifFiles.get().files.toList()
        if (inputs.isEmpty()) return

        val first = readSarif(inputs.first())
        val others = inputs.subList(1, inputs.size).map { readSarif(it) }

        for (map in others) {
            first.getResultsOfFirstRun.addAll(map.getResultsOfFirstRun)
        }

        writeSarif(outputFile.get().asFile, first)
    }

    private fun writeSarif(out: File, first: JsonElement) {
        out.bufferedWriter(Charsets.UTF_8).use {
            gson.toJson(first, it)
        }
    }


    private fun readSarif(first: File): JsonElement {
        first.reader().use {
            return gson.fromJson(it, JsonElement::class.java)!!
        }
    }
}
val gson: Gson = GsonBuilder().setPrettyPrinting().create()
