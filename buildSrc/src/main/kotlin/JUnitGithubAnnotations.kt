import org.w3c.dom.NodeList
import java.nio.file.Path
import javax.xml.parsers.DocumentBuilderFactory
import javax.xml.xpath.XPathConstants
import javax.xml.xpath.XPathFactory
import kotlin.io.path.extension
import kotlin.io.path.name
import kotlin.io.path.walk

object JUnitGithubAnnotations {
    private val xqryTestcase by lazy {
        val xPath = XPathFactory.newInstance().newXPath()
        val expression = "/testsuite/testcase[./failure]"
        xPath.compile(expression)
    }

    private val xqryFailureMessage by lazy {
        val xPath = XPathFactory.newInstance().newXPath()
        val expression = "./failure/@message"
        xPath.compile(expression)
    }

    @JvmStatic
    fun readAndPrint(f: Path) {
        val builder = DocumentBuilderFactory.newInstance().newDocumentBuilder()
        val doc = builder.parse(f.toFile())
        val nodeList = xqryTestcase.evaluate(doc, XPathConstants.NODESET) as NodeList

        if (nodeList.length <= 0) {
            return
        }


        // module name assuming <mod>/build/test-results/test/<file>.xml
        val base = f.parent.parent.parent.parent.name
        for (i in 0 until nodeList.length) {
            val node = nodeList.item(i)
            // failure in test case
            val failure = xqryFailureMessage.evaluate(node, XPathConstants.STRING) as String?
            val attributes = node.attributes
            val caseName = attributes.getNamedItem("name").textContent
            val classname = attributes.getNamedItem("classname").textContent
            val filename = "$base/${classname.replace(".", "/")}"
            val message = failure?.take(80) ?: ""
            // ::error file={name},line={line},endLine={endLine}, ={title}::{message}
            print("::error title=Testcase-missed,file=$filename::Error in test case '$caseName' and $message")
        }
    }

    @JvmStatic
    fun readAndPrintAll(root: Path) {
        val reports = root.fileSystem.getPathMatcher("glob:TEST-*xml")
        root.walk()
            .filter { it.extension == "xml" }
            .filter { reports.matches(it) }
            .forEach { readAndPrint(it) }
    }
}