/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package view

import javafx.beans.binding.Bindings
import javafx.scene.control.*
import javafx.scene.text.Font
import org.key_project.util.java.IOUtil
import org.slf4j.LoggerFactory
import tornadofx.*
import java.io.BufferedReader
import java.io.File
import java.io.FileReader
import java.io.IOException
import java.nio.charset.StandardCharsets
import java.nio.file.Paths
import java.util.*
import javax.swing.tree.TreePath


data class TreeValue(
    val label: String,
    val example: Example? = null,
    val children: MutableList<TreeValue> = arrayListOf()
)

/**
 * Dialog to choose an example to load.
 * May be opened automatically when KeY starts.
 */
class ExampleChooser(val examplesDir: File) : Dialog<File>() {
    val selectedExampleProperty = objectProperty<Example?>(null)
    var selectedExample by selectedExampleProperty

    private var exampleList: TreeView<TreeValue> by singleAssign()
    private var tabPane: TabPane by singleAssign()

    private val root = splitpane {
        titledpane("Examples") {
            isAnimated=false
            isCollapsible=false
            val examples = listExamples(examplesDir)
            val root = TreeValue("/")
            examples.forEach { addToRoot(it, root, it.path.iterator()) }
            exampleList = treeview(TreeItem(root)) {
                isShowRoot = false
                selectionModel.selectionMode = SelectionMode.SINGLE
                onUserSelect {
                    selectedExample = it.example
                }
                cellFormat { text = it.label }
                populate { it.value.children }
            }
        }
        tabPane = tabpane {

        }
        setDividerPositions(.3)
    }

    init {
        dialogPane.content = root
        val load = ButtonType("Load", ButtonBar.ButtonData.APPLY)
        val loadProof = ButtonType("Load Proof", ButtonBar.ButtonData.FINISH)
        val close = ButtonType.CANCEL
        dialogPane.buttonTypes.setAll(load, loadProof, close)


        val hasSelectedExample = selectedExampleProperty.isNotNull
        (dialogPane.lookupButton(load) as Button).enableWhen(hasSelectedExample)
        (dialogPane.lookupButton(loadProof) as Button).enableWhen(hasSelectedExample)

        setResultConverter {
            when (it.buttonData) {
                ButtonBar.ButtonData.APPLY -> {
                    close()
                    selectedExample?.obligationFile
                }
                else -> null
            }
        }




        // create example list

        /*loadButton = JButton("Load Example")
        loadButton.addActionListener(ActionListener { e: ActionEvent? ->
            if (selectedExample == null) {
                throw RuntimeException("No example selected")
            }
            fileToLoad = selectedExample!!.obligationFile
            setVisible(false)
        })
        buttonPanel.add(loadButton)
        getRootPane().setDefaultButton(loadButton)

        // create "load proof" button
        loadProofButton = JButton("Load Proof")
        loadProofButton.addActionListener(ActionListener { e: ActionEvent? ->
            checkNotNull(selectedExample) { "No example selected" }
            check(selectedExample!!.hasProof()) { "Selected example has no proof." }
            fileToLoad = selectedExample!!.proofFile
            setVisible(false)
        })
        buttonPanel.add(loadProofButton)

        // create "cancel" button
        cancelButton = JButton("Cancel")
        cancelButton.addActionListener(ActionListener { e: ActionEvent? ->
            fileToLoad = null
            setVisible(false)
        })
        buttonPanel.add(cancelButton)
        GuiUtilities.attachClickOnEscListener(cancelButton)

        // select first example
        val firstLeaf: DefaultMutableTreeNode = (model.getRoot() as DefaultMutableTreeNode).getFirstLeaf()
        val pathToFirstLeaf = TreePath(firstLeaf.getPath())
        exampleList.selectionModel.setSelectionPath(pathToFirstLeaf)
        exampleList.makeVisible(pathToFirstLeaf)

        // show
        getContentPane().setLayout(BoxLayout(getContentPane(), BoxLayout.Y_AXIS))
         */
        dialogPane.setPrefSize(800.0, 400.0)

        selectedExampleProperty.onChange {
            if (it != null) updateDescription(it) else {
                tabPane.tabs.clear()
                /*selectedExample = null
            loadButton.setEnabled(false)
            loadProofButton.setEnabled(false)
             */
            }
        }
    }

    private tailrec fun addToRoot(example: Example, node: TreeValue, path: Iterator<String>) {
        if (path.hasNext()) {
            val p = path.next()
            val c = node.children.find { it.label == p }
            val n = c ?: TreeValue(p, null).also { node.children.add(it) }
            addToRoot(example, n, path)
        } else {
            node.children.add(TreeValue(example.name, example))
        }
    }


    private fun updateDescription(nodeObj: Example) {
        tabPane.tabs.clear()
        addTab(nodeObj.description, "Description", true)
        val fileAsString = nodeObj.obligationFile.readText()
        val p = fileAsString.lastIndexOf("\\problem")
        if (p >= 0) {
            addTab(fileAsString.substring(p), "Proof Obligation", false)
        }
        for (file in nodeObj.additionalFiles) {
            addTab(fileAsString(file), file.getName(), false)
        }
        //loadButton.setEnabled(true)
        //loadProofButton.setEnabled(nodeObj.hasProof())
        selectedExample = nodeObj
    }

    private fun addTab(string: String, name: String, wrap: Boolean) {
        val area = TextArea(string)
        area.font = Font("monospace", area.font.size)
        area.positionCaret(0)
        area.isEditable = false
        area.isWrapText = wrap
        val tab = Tab(name, area)
        tab.isClosable = false
        tabPane.tabs.add(tab)
    }

    companion object {
        /**
         * This path is also accessed by the Eclipse integration of KeY to find the right examples.
         */
        const val EXAMPLES_PATH = "examples"

        /**
         * This constant is accessed by the eclipse based projects.
         */
        const val KEY_FILE_NAME = "project.key"
        const val PROOF_FILE_NAME = "project.proof"

        /**
         * Java property name to specify a custom key example folder.
         */
        const val KEY_EXAMPLE_DIR = "key.examples.dir"
        val LOGGER = LoggerFactory.getLogger(ExampleChooser::class.java)

        /**
         * This class is a singleton class and this its only instance.
         */
        private var instance: ExampleChooser? = null

        // -------------------------------------------------------------------------
        // internal methods
        // -------------------------------------------------------------------------
        fun lookForExamples(): File {
            // weigl: using java properties: -Dkey.examples.dir="..."
            if (System.getProperty(KEY_EXAMPLE_DIR) != null) {
                return File(System.getProperty(KEY_EXAMPLE_DIR))
            }

            return File("key.ui/examples").absoluteFile

        }

        private fun fileAsString(f: File): String {
            return try {
                IOUtil.readFrom(f)
            } catch (e: IOException) {
                LOGGER.error("Could not read file '{}'", f, e)
                "<Error reading file: $f>"
            }
        }

        fun extractDescription(
            file: File, sb: StringBuilder,
            properties: Properties
        ): StringBuilder {
            val lines = file.readLines()
            var emptyLineSeen = false
            for (line in lines) {
                if (emptyLineSeen) {
                    sb.append(line).append("\n")
                } else {
                    val trimmed = line.trim { it <= ' ' }
                    if (trimmed.isEmpty()) {
                        emptyLineSeen = true
                    } else if (trimmed.startsWith("#")) {
                        // ignore
                    } else {
                        val entry = trimmed.split(" *[:=] *".toRegex(), limit = 2).toTypedArray()
                        if (entry.size > 1) {
                            properties[entry[0]] = entry[1]
                        }
                    }
                }
            }
            return sb
        }

        /**
         * Shows the dialog, using the passed examples directory. If null is passed, tries to find
         * examples directory on its own.
         */
        fun showInstance(examplesDirString: String? = null): File? {
            // get examples directory
            val examplesDir: File = examplesDirString?.let { File(examplesDirString) } ?: lookForExamples()
            if (!examplesDir.isDirectory()) {
                alert(
                    Alert.AlertType.ERROR, "Error loading examples",
                    """
                        The examples directory cannot be found.
                        Please install them at ${
                        examplesDirString ?: IOUtil.getProjectRoot(ExampleChooser::class.java).toString()
                    }/
                        """
                )
                return null
            }
            // show dialog
            val dialog = instance ?: ExampleChooser(examplesDir)
            instance = dialog
            return dialog.showAndWait().orElse(null)
        }

        /**
         * Lists all examples in the given directory. This method is also accessed by the eclipse based
         * projects.
         *
         * @param examplesDir The examples directory to list examples in.
         * @return The found examples.
         */
        fun listExamples(examplesDir: File): List<Example> {
            val result: MutableList<Example> = LinkedList()
            val index = examplesDir / "index" / "samplesIndex.txt"

            try {
                for (read in index.readLines()) {
                    val line = read.trim { it <= ' ' }
                    if (line.startsWith("#") || line.isEmpty()) {
                        continue
                    }
                    val f = examplesDir / line
                    try {
                        result.add(Example(f))
                    } catch (e: IOException) {
                        LOGGER.warn("Cannot parse example {}; ignoring it.", f, e)
                    }
                }
            } catch (e: IOException) {
                LOGGER.warn("Error while reading samples", e)
            }
            return result
        }
    }
}

private operator fun File.div(s: String) = File(this, s)

/**
 * This class wraps a [File] and has a special [.toString] method only using the
 * short file name w/o path.
 *
 *
 * Used for displaying files in the examples list w/o prefix
 */
class Example(val exampleFile: File) {
    val directory: File = exampleFile.getParentFile()
    private val properties: Properties = Properties()
    val description: String

    init {
        val sb = StringBuilder()
        ExampleChooser.extractDescription(exampleFile, sb, properties)
        description = sb.toString()
    }

    val proofFile: File
        get() = File(directory, properties.getProperty(KEY_PROOF_FILE, ExampleChooser.PROOF_FILE_NAME))
    val obligationFile: File
        get() = File(directory, properties.getProperty(KEY_FILE, ExampleChooser.KEY_FILE_NAME))
    val name: String
        get() = properties.getProperty(KEY_NAME, directory.getName())
    val additionalFiles: List<File>
        get() {
            val result = ArrayList<File>()
            var i = 1
            while (properties.containsKey(ADDITIONAL_FILE_PREFIX + i)) {
                result.add(File(directory, properties.getProperty(ADDITIONAL_FILE_PREFIX + i)))
                i++
            }
            return result
        }
    val exportFiles: List<File>
        get() {
            val result = ArrayList<File>()
            var i = 1
            while (properties.containsKey(EXPORT_FILE_PREFIX + i)) {
                result.add(File(directory, properties.getProperty(EXPORT_FILE_PREFIX + i)))
                i++
            }
            return result
        }
    val path: Array<String>
        get() = properties.getProperty(KEY_PATH, DEFAULT_CATEGORY_PATH).split("/".toRegex())
            .dropLastWhile { it.isEmpty() }
            .toTypedArray()

    companion object {
        /**
         * The default category under which examples range if they do not have [.KEY_PATH]
         * set.
         */
        private const val DEFAULT_CATEGORY_PATH = "Unsorted"

        /**
         * The [Properties] key to specify the path in the tree.
         */
        private const val KEY_PATH = "example.path"

        /**
         * The [Properties] key to specify the name of the example. Directory name if left
         * open.
         */
        private const val KEY_NAME = "example.name"

        /**
         * The [Properties] key to specify the file for the example. KEY_FILE_NAME by default
         */
        private const val KEY_FILE = "example.file"

        /**
         * The [Properties] key to specify the proof file in the tree. May be left open
         */
        private const val KEY_PROOF_FILE = "example.proofFile"

        /**
         * The [Properties] key to specify the path in the tree. Prefix to specify additional
         * files to load. Append 1, 2, 3, ...
         */
        private const val ADDITIONAL_FILE_PREFIX = "example.additionalFile."

        /**
         * The [Properties] key to specify the path in the tree. Prefix to specify export
         * files which are not shown as tabs in the example wizard but are extracted to Java
         * projects in the Eclipse integration. Append 1, 2, 3, ...
         */
        private const val EXPORT_FILE_PREFIX = "example.exportFile."
    }
}
