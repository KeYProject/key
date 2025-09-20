import org.w3c.dom.Element
import java.io.PrintWriter
import java.nio.file.Path
import java.nio.file.Paths
import javax.xml.parsers.DocumentBuilderFactory
import kotlin.io.path.exists

object CheckstyleMarkdownReport {
    @JvmStatic
    fun report(xmlFile: Path, targetFile: Path, projectDir: Path) {
        if (!xmlFile.exists()) return

        // get variables either from the environment
        val sha = System.getenv("GITHUB_SHA") ?: "main"
        val host = System.getenv("GITHUB_SERVER_URL") ?: "https://github.com"
        val repo = System.getenv("GITHUB_REPOSITORY") ?: "keyproject/key"
        val baseUrl = "$host/$repo/blob/$sha"

        val docBuilder = DocumentBuilderFactory.newInstance().newDocumentBuilder()
        val doc = docBuilder.parse(xmlFile.toFile())
        doc.documentElement.normalize()

        PrintWriter(targetFile.toFile()).use { out ->
            out.write("\n\n")

            val files = doc.getElementsByTagName("file")
            for (i in 0 until files.length) {
                val fileNode = files.item(i) as Element
                val filePath = Paths.get(fileNode.getAttribute("name"))
                val relativePath = projectDir.relativize(filePath).toString()
                val url = "$baseUrl/$relativePath"

                out.write("#### $relativePath\n\n")

                val errors = fileNode.getElementsByTagName("error")
                for (j in 0 until errors.length) {
                    val error = errors.item(j) as Element
                    val severity = error.getAttribute("severity")
                    val message = error.getAttribute("message")
                    val line = error.getAttribute("line")
                    val column = error.getAttribute("column")
                    out.write("\n* $severity [$message @$line:$column]")
                }

                out.write("\n\n")
            }
        }
    }
}