package io.github.wadoon.key

import io.github.wadoon.key.view.ProofTree
import javafx.application.Application
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import javafx.scene.Parent
import javafx.scene.control.TreeItem
import org.fxmisc.richtext.CodeArea
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.material2.Material2AL
import tornadofx.*
import java.awt.event.KeyEvent
import java.io.File
import java.nio.file.Path
import java.nio.file.Paths
import javax.swing.JMenu
import javax.swing.event.MenuEvent
import javax.swing.event.MenuListener
import kotlin.io.path.isDirectory
import kotlin.io.path.isRegularFile
import kotlin.io.path.listDirectoryEntries


fun main(args: Array<String>) {
    Application.launch(KeyApp::class.java)
}

class KeyApp : App(KMainView::class)

class GlobalData {
    val workspace: Path = Paths.get(".")
}

class GlobalDataModel(data: GlobalData = GlobalData()) : ItemViewModel<GlobalData>(data) {
    val workspacePath = bind(GlobalData::workspace)
}


class KMainView : View("KeY") {
    val globalData: GlobalDataModel by inject()

    override val root = borderpane {
        top<TopView>()
        left = drawer {
            item(OpenProofs::class, expanded = true)
            item(ProofTree::class, expanded = true)
            item(StrategySettings::class)
            //item(TreeFolderView::class)
        }

        right = drawer {
            item(SourceView::class)
        }

        bottom = drawer {

        }

        center<CenterView>()

    }
}



class StrategySettings : View("Strategy") {
    override val root = vbox {

    }
}

class OpenProofs : View("Proofs") {
    override val root = vbox {
        toolbar()
        treeview(TreeItem<String>("No proof loaded")) {}
    }
}

class SourceView : View("Source") {
    var codeArea by singleAssign<CodeArea>()
    override val root: Parent = hbox {
        toolbar {}
        codeArea = CodeArea()
        add(codeArea)
    }
}

class TreeFolderView : View("Tree Folder View") {
    val globalData: GlobalDataModel by inject()

    private val rootNodeProperty = property<FileTreeItem?>()
    var rootNode by rootNodeProperty

    override val root: Parent = hbox {
        rootNode = globalData.workspacePath.value?.let { FileTreeItem(it) }
        treeview(rootNode) {
            globalData.workspacePath.onChange {
                rootNode = it?.let { FileTreeItem(it) }
            }
            rootNodeProperty.fxProperty.onChange {
                this.root = it
            }
        }
    }
}

class FileTreeItem(file: Path) : TreeItem<Path>(file) {
    private val isLeafProp by lazy { value.isRegularFile() }
    private val childrenProp: ObservableList<FileTreeItem> by lazy {
        val f = value
        if (f != null && f.isDirectory()) {
            val files = f.listDirectoryEntries()
            val children = FXCollections.observableArrayList<FileTreeItem>()
            for (childFile in files) {
                children.add(FileTreeItem(childFile))
            }
            children
        } else {
            FXCollections.emptyObservableList()
        }
    }

    override fun getChildren(): ObservableList<TreeItem<Path>> {
        if (super.getChildren().isEmpty() && !isLeafProp) {
            super.getChildren().setAll(childrenProp)
        }
        return super.getChildren()
    }

    override fun isLeaf(): Boolean = isLeafProp
}

class TopView : View() {
    private val globalData: GlobalDataModel by inject()

    override val root: Parent = vbox {
        menubar {
            menu("File") {
                item("Open Examples") { }
                item("Open File...") {}
                item("Recent files") {}
                item("editMostRecentFileAction") {}
                item("saveFileAction") {}
                item("saveBundleAction") {}
                item("quickSaveAction")
                item("quickLoadAction")
                separator()
                item("proofManagementAction")
                item("loadUserDefinedTacletsAction")
                menu("Prove") {
                    item("loadUserDefinedTacletsForProvingAction")
                    item("loadKeYTaclets")
                    item("lemmaGenerationBatchModeAction")
                    item("runAllProofsAction")
                }
                separator()
                menu("recentFileMenu") {}
                separator()
                item("exitMainAction") {}
            }

            menu("_View") {
                isMnemonicParsing = true
                checkmenuitem("Toogle Pretty Printing") {}
                checkmenuitem("Toogle Unicode ") {}
                checkmenuitem("Toogle Syntax Highlighting") {}
                menu("Term Labels") {}

                checkmenuitem("hidePackagePrefixToggleAction")
                checkmenuitem("toggleSequentViewTooltipAction")
                checkmenuitem("toggleSourceViewTooltipAction")

                separator()
                menu("Font Size") {
                    item("Decrease font size")
                    item("Inccrease font size")
                }
                item("ToolTipOptionsAction")
                item("ProofDiffFrame")
                separator()

                item("createSelectionMenu")

                separator()
                item("selectionBackAction")
                item("selectionForwardAction")
                separator()
            }

            menu("Proof") {
                item("auto")
                item("go back")
                item("prune")
                item("AbandonTaskAction")
                separator()
                item("SearchInProofTreeAction")
                item("SearchInSequentAction")
                item("SearchNextAction")
                item("SearchPreviousAction")
                menu("Search Mode") {
                }
                separator()
                item("ShowUsedContractsAction")
                item("ShowActiveTactletOptionsAction")
                item("showActiveSettingsAction")
                item("ShowProofStatistics")
                item("ShowKnownTypesAction")
            }

            menu("_Options") {
                isMnemonicParsing = true
                item("Show Settings")
                item("Taclet Options")
                item("SMT Settings")
                separator()
                checkmenuitem("Confirm exit")
                checkmenuitem("Auto save")
                checkmenuitem("Right Mouse Click Toggle")
                checkmenuitem("Ensure Source Consistency")
            }
            menu("_About") {
                item("About")
                item("Homepage")
                item("Send Feedback")
                item("License Action")
            }
        }

        toolbar {
            button("Open Workspace", FontIcon(Material2AL.FOLDER_OPEN)) {
                action {
                    val file = chooseDirectory("Select workspace", File("."))
                    globalData.workspacePath.setValue(file?.toPath())
                }
            }
        }
    }
}

class CenterView : View("") {
    private var currentGoal: SequentView by singleAssign()

    private val rootPane = splitpane {
        tabpane {
            currentGoal = SequentView()
            tab("Current Goal", currentGoal)
        }
    }
    val components = FXCollections.observableArrayList<ObservableList<View>>()
    override val root: Parent = rootPane
}

class SequentView : Fragment("Current Sequent") {
    val child: CodeArea = CodeArea().also {
        it.isEditable = false
    }
    override val root: Parent = child
}