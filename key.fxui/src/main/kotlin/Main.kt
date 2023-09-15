package io.github.wadoon.key

import de.uka.ilkd.key.control.DefaultUserInterfaceControl
import de.uka.ilkd.key.control.KeYEnvironment
import de.uka.ilkd.key.java.Services
import de.uka.ilkd.key.java.abstraction.KeYJavaType
import de.uka.ilkd.key.logic.op.IObserverFunction
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo
import de.uka.ilkd.key.proof.Goal
import de.uka.ilkd.key.proof.Node
import de.uka.ilkd.key.proof.Proof
import de.uka.ilkd.key.proof.ProofAggregate
import de.uka.ilkd.key.proof.init.IPersistablePO
import de.uka.ilkd.key.proof.init.ProblemInitializer
import de.uka.ilkd.key.proof.io.AbstractProblemLoader
import de.uka.ilkd.key.prover.TaskFinishedInfo
import de.uka.ilkd.key.prover.TaskStartedInfo
import de.uka.ilkd.key.speclang.Contract
import de.uka.ilkd.key.util.KeYTypeUtil
import io.github.wadoon.key.controls.*
import io.github.wadoon.key.view.ProofTree
import io.github.wadoon.key.view.SetStatusBar
import io.github.wadoon.key.view.StatusBar
import javafx.application.Application
import javafx.beans.binding.Bindings
import javafx.beans.binding.ObjectBinding
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import javafx.geometry.Orientation
import javafx.geometry.Side
import javafx.scene.Parent
import javafx.scene.control.*
import javafx.scene.layout.Priority
import org.fxmisc.richtext.CodeArea
import org.key_project.util.collection.ImmutableSet
import org.kordamp.ikonli.Ikon
import org.kordamp.ikonli.fontawesome.FontAwesome
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.material2.Material2AL
import org.kordamp.ikonli.material2.Material2MZ
import tornadofx.*
import view.ExampleChooser
import view.chooseContract
import java.io.File
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.io.path.isDirectory
import kotlin.io.path.isRegularFile
import kotlin.io.path.listDirectoryEntries


fun main(args: Array<String>) {
    Application.launch(KeyApp::class.java)
}

class KeyApp : App(KMainView::class)

class GlobalData : Component(), ScopedInstance {
    val workspacePathProperty = property(Paths.get("."))
    var workspacePath by workspacePathProperty

    val selectedProofProperty = property<Proof?>(null)
    var selectedProof: Proof? by selectedProofProperty

    val selectedNodeProperty = property<Node?>(null)
    var selectedNode: Node? by selectedNodeProperty

    val selectedGoalProperty = property<Goal?>(null)
    var selectedGoal: Goal? by selectedGoalProperty


    val openProofsProperty = listProperty<Proof>()
    val openProofs by openProofsProperty


    val servicesProperty: ObjectBinding<Services?> =
        Bindings.createObjectBinding(
            { selectedProofProperty.fxProperty.value?.services },
            selectedProofProperty.fxProperty
        )
    val services: Services? by servicesProperty
}


//class GlobalDataModel(data: GlobalData = GlobalData()) : ItemViewModel<GlobalData>(data) {

class KMainView : View("KeY") {
    val globalData: GlobalData by inject()

    override val root = borderpane {
        top<TopView>()

        center = splitpane {
            drawer(multiselect = true) {
                item(OpenProofs::class, expanded = true)
                item(ProofTree::class, expanded = true)
                item(StrategySettings::class)
                //item(TreeFolderView::class)
            }

            splitpane(Orientation.VERTICAL) {
                add(find<CenterView>().root)
                vbox {
                    drawer(Side.BOTTOM, multiselect = true, floatingContent = true) {
                        item("Test", FontIcon(Material2AL.ALBUM), expanded = false, showHeader = true) {
                            add(Label("Only a test panel"))
                        }
                    }
                }
            }

            drawer(Side.RIGHT, multiselect = true) {
                item(SourceView::class)
            }
        }

        bottom<StatusBar>()
    }

    init {
        fire(SetStatusBar("Loaded", FontAwesome.ROCKET))
    }
}


class StrategySettings : View("Strategy") {
    override val root = vbox {

    }
}

class OpenProofs : View("Proofs") {
    val globalData: GlobalData by inject()

    override val root = vbox {
        toolbar {
            label("Open Proofs")
            spacer()
            button(graphic = FontIcon(FontAwesome.TRASH))
            button(graphic = FontIcon(FontAwesome.REORDER))
        }
        listview(globalData.openProofsProperty) {
            placeholder = Label("No proofs loaded")
        }
    }
}

class SourceView : View("Source") {
    var codeArea by singleAssign<CodeArea>()
    override val root: Parent = vbox {
        toolbar {}
        codeArea = CodeArea()
        add(codeArea)
    }
}

class TreeFolderView : View("Tree Folder View") {
    val globalData: GlobalData by inject()

    private val rootNodeProperty = property<FileTreeItem?>()
    var rootNode by rootNodeProperty

    override val root: Parent = hbox {
        rootNode = globalData.workspacePath.let { FileTreeItem(it) }
        treeview(rootNode) {
            globalData.workspacePathProperty.fxProperty.onChange {
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
    private val globalData: GlobalData by inject()

    override val root: Parent = vbox {
        menubar {
            menu("File") {
                item("Open Examples") { }
                item("Open File...") {}
                item("Recent files") {}
                item("editMostRecentFileAction") {}
                item("Save") {}
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
                item("exitMainAction", graphic = FontIcon(FontAwesome.WINDOW_CLOSE)) {}
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
                hgrow = Priority.ALWAYS
            }
            menu("_About") {
                item("About", graphic = FontIcon(FontAwesome.QUESTION_CIRCLE_O))
                item("Homepage", graphic = FontIcon(FontAwesome.WORDPRESS))
                item("Send Feedback", graphic = FontIcon(FontAwesome.MAIL_FORWARD))
                item("License Action", graphic = FontIcon(FontAwesome.DRIVERS_LICENSE))
            }
        }

        /*
        toolbar {
            button("Open Workspace", FontIcon(Material2AL.FOLDER_OPEN)) {
                action {
                    val file = chooseDirectory("Select workspace", File("."))
                    globalData.workspacePath = file?.toPath()
                }
            }

            menubutton(graphic = FontIcon(FontAwesome.ARROW_DOWN)) {
                item("Run Z3_FP")
                item("Run Z3_FP")
            }

            button(graphic = FontIcon(FontAwesome.BACKWARD)) {

            }

            button(graphic = FontIcon(FontAwesome.SCISSORS)) {

            }
            button(graphic = FontIcon(FontAwesome.UNDO)) {

            }
            button(graphic = FontIcon(FontAwesome.FOLDER_OPEN)) {

            }
            button(graphic = FontIcon(FontAwesome.STEP_FORWARD)) {

            }
            button(graphic = FontIcon(FontAwesome.CODEPEN)) {

            }
            button(graphic = FontIcon(FontAwesome.SAVE)) {

            }
            button(graphic = FontIcon(FontAwesome.SAVE)) {

            }
            button(graphic = FontIcon(FontAwesome.TASKS)) {

            }

            button(graphic = FontIcon(FontAwesome.TASKS)) {

            }

            button(graphic = FontIcon(Material2AL.DO_NOT_STEP))
            button(graphic = FontIcon(FontAwesome.BOMB))
            button(graphic = FontIcon(Material2AL.ADB))

        }
        */
        ribbon {
            quickAccessBar {

            }
            tab("Home") {
                group("File", fontIcon = FontAwesome.FILE) {
                    //item(control = Button("Open"))
                    button(fontIcon = FontAwesome.PENCIL_SQUARE) {
                        contentDisplay = ContentDisplay.TOP
                        text = "Open File"
                        styleClass.add("big")
                        graphic = FontIcon(FontAwesome.FOLDER_OPEN)

                        action {
                            val file = chooseDirectory("Select workspace", globalData.workspacePath.toFile())
                            if (file != null) {
                                globalData.workspacePath = file.toPath()

                                loadFile(file)
                            }
                        }
                    }
                    button("Open Examples", FontAwesome.ENVELOPE_OPEN) {
                        action {
                            val example = ExampleChooser.showInstance()
                            example?.let{loadFile(it) }
                        }
                    }
                    button("Recent files", FontAwesome.PENCIL_SQUARE) {}
                    button("Edit Most Recent File", fontIcon = FontAwesome.PENCIL_SQUARE) {}
                    button("Save", fontIcon = FontAwesome.SAVE) {}
                    button("Save Bundle", fontIcon = FontAwesome.FILE_ZIP_O) {}
                }

                group(fontIcon = (FontAwesome.FILE)) {
                    column {
                        button("Quick Save")
                        button("Quick Load")
                    }
                }

                group("Management", (FontAwesome.FILE)) {
                    button("Manager", fontIcon = Material2AL.BARCODE)
                }

                group("View", (FontAwesome.FILE), graphic = FontIcon(FontAwesome.FILE)) {
                    column {
                        checkmenuitem("Toogle Pretty Printing") {}
                        checkmenuitem("Toogle Unicode ") {}
                        checkmenuitem("Toogle Syntax Highlighting") {}
                    }
                    column {
                        checkmenuitem("Hide Package Prefix")
                        checkmenuitem("Sequent Tooltip")
                        checkmenuitem("Source View Tooltips")
                    }
                    item("Term Labels", control = MenuButton()) {}

                    /*
                    //separator()
                    menu("Font Size") {
                        item("Decrease font size")
                        item("Inccrease font size")
                    }
                    item("ToolTipOptionsAction")
                    item("ProofDiffFrame")
                    //separator()

                    item("createSelectionMenu")

                    separator()
                    item("selectionBackAction")
                    item("selectionForwardAction")
                    separator()*/
                }

                group("Navigation", fontIcon = FontAwesome.FILE) {
                    button("selectionBackAction", (FontAwesome.PENCIL_SQUARE))
                    button("selectionForwardAction", (FontAwesome.PENCIL_SQUARE))
                }
            }

            tab("Proof")
            {
                styleClass.add("orange")
                group("Control") {
                    button("Auto", fontIcon = FontAwesome.PLAY_CIRCLE)
                    button("Undo", fontIcon = FontAwesome.BACKWARD)
                    button("Prune", fontIcon = FontAwesome.SCISSORS)
                    button("Abandon", fontIcon = FontAwesome.TRASH_O)
                }

                group("Navigation", fontIcon = FontAwesome.FILE) {
                    button("Back", (FontAwesome.BACKWARD))
                    button("Forward", (FontAwesome.FORWARD))
                }

                group("Find") {
                    button("Find in Tree", fontIcon = Material2MZ.WATER_DAMAGE)
                    button("Find in Sequent", fontIcon = FontAwesome.MAGNET)
                    button("Next")
                    button("Previous")
                }

                group("Information") {
                    column {
                        button("Taclet Options")
                        button("Active Settings")
                    }
                    button("Statistics")
                    button("Show")
                    button("Used Contracts")
                }
            }

            tab("Tools") {
                group("Taclets") {
                    button("User Defined Taclets")
                }
                group("Prove") {
                    button("Prove User-Defined Taclets")
                    button("Load KeY Taclets")
                    button("Lemma Gneration Batch Mode")
                    button("Run All Proofs")
                }

                group("Slicing") {

                }
            }
        }
    }

    private fun loadFile(file: File?) {
        val ui = object : DefaultUserInterfaceControl(null) {
            override fun loadingStarted(loader: AbstractProblemLoader?) {
                super.loadingStarted(loader)
            }

            override fun loadingFinished(
                loader: AbstractProblemLoader?,
                poContainer: IPersistablePO.LoadedPOContainer,
                proofList: ProofAggregate,
                result: AbstractProblemLoader.ReplayResult
            ) {
                super.loadingFinished(loader, poContainer, proofList, result)
                fire(SetStatusBar("Task Finished: " + proofList.size()))
            }

            override fun taskStarted(info: TaskStartedInfo?) {
                super.taskStarted(info)
                fire(SetStatusBar("Task Started: " + info))

            }

            override fun taskProgress(position: Int) {
                super.taskProgress(position)
                fire(SetStatusBar("Task Progress:" + position))
            }

            override fun taskFinished(info: TaskFinishedInfo?) {
                super.taskFinished(info)
                fire(SetStatusBar("Task Finished: " + info))
            }

            override fun proofCreated(
                sender: ProblemInitializer?,
                proofAggregate: ProofAggregate?
            ) {
                super.proofCreated(sender, proofAggregate)
                fire(SetStatusBar("Proof Created"))
            }

            override fun macroStarted(info: TaskStartedInfo?) {
                super.macroStarted(info)
                fire(SetStatusBar(info.toString()))
            }

            override fun macroFinished(info: ProofMacroFinishedInfo?) {
                super.macroFinished(info)
                fire(SetStatusBar(info.toString()))
            }
        }
        val loader = ui.load(
            null,
            file, mutableListOf(), null, mutableListOf(),
            null, false, null
        )
        val initConfig = loader.initConfig

        val env = KeYEnvironment(
            ui, initConfig, loader.proof,
            loader.proofScript, loader.result
        )

        if (loader.proof != null) {
            val allContracts = mutableListOf<Contract>()
            val kjts: Set<KeYJavaType> = env.javaInfo.getAllKeYJavaTypes()
            for (type in kjts) {
                if (!KeYTypeUtil.isLibraryClass(type)) {
                    val targets: ImmutableSet<IObserverFunction> =
                        env.specificationRepository.getContractTargets(type)
                    for (target in targets) {
                        val contracts: ImmutableSet<Contract> =
                            env.specificationRepository.getContracts(type, target)
                        allContracts.addAll(contracts)
                    }
                }
            }
            val contract = chooseContract(env.services, allContracts)
            if (contract != null) {
                val proofOblInput = contract.createProofObl(env.initConfig, contract)
                val proof = env.createProof(proofOblInput)
                globalData.selectedProof = proof
                globalData.selectedGoal = proof.openGoals().head()
                globalData.selectedNode = proof.root()
            }
        }
    }

    private fun RibbonGroup.column(block: Column.() -> Unit): Column = Column().also {
        it.block()
        nodes.add(it)
    }


    fun RibbonGroup.button(
        text: String = "",
        fontIcon: Ikon? = null,
        graphic: javafx.scene.Node? = null,
        op: Button.() -> Unit = {}
    ) =
        Button(text).also {
            it.contentDisplay = ContentDisplay.TOP
            graphic?.let { g -> it.graphic = g }
            fontIcon?.let { i -> it.graphic = FontIcon(i).also { icon -> icon.setIconSize(24) } }
            it.isWrapText = true
            it.textOverrun = OverrunStyle.CLIP
            it.setMinSize(Button.USE_PREF_SIZE, Button.USE_PREF_SIZE)
            it.styleClass.add("big")
            it.op()
            nodes.add(it)
        }

    fun Column.button(text: String = "", graphic: javafx.scene.Node? = null, op: Button.() -> Unit = {}) =
        Button(text).also {
            it.contentDisplay = ContentDisplay.RIGHT
            if (graphic != null) it.graphic = graphic
            it.op()
            add(it)
        }

    private fun RibbonGroup.item(
        title: String = "", graphic: javafx.scene.Node? = null,
        control: javafx.scene.Node? = null, block: RibbonItem.() -> Unit = {}
    ): RibbonItem {
        val item = RibbonItem()
        item.label = title
        item.graphic = graphic
        item.item = control
        item.block()
        this.nodes.add(item)
        return item
    }

    private fun Column.item(
        title: String = "", graphic: javafx.scene.Node? = null,
        control: javafx.scene.Node? = null, block: RibbonItem.() -> Unit = {}
    ): RibbonItem {
        val item = RibbonItem()
        item.label = title
        item.graphic = graphic
        item.item = control
        item.block()
        this.add(item)
        return item
    }


    private fun RibbonTab.group(
        title: String = "", fontIcon: Ikon? = null,
        graphic: javafx.scene.Node? = null,
        block: RibbonGroup.() -> Unit = {}
    ): RibbonGroup {
        val group = RibbonGroup()
        //group.title = title
        group.graphic = graphic
        fontIcon?.let { group.graphic = FontIcon(fontIcon) }
        group.block()
        this.ribbonGroups.add(group)
        return group
    }

    private fun Parent.ribbon(block: Ribbon.() -> Unit = {}): Ribbon {
        val ribbon = Ribbon()
        opcr(this, ribbon, block)
        return ribbon
    }

    private fun Ribbon.tab(
        title: String = "", graphic: javafx.scene.Node? = null,
        block: RibbonTab.() -> Unit = {}
    ): RibbonTab {
        val tab = RibbonTab(title)
        tab.graphic = graphic
        tab.block()
        this.tabs.add(tab)
        return tab
    }


    private fun Ribbon.quickAccessBar(block: QuickAccessBar.() -> Unit): QuickAccessBar {
        val qab = QuickAccessBar()
        qab.block()
        this.quickAccessBar = qab
        return qab
    }

    private fun RibbonGroup.checkmenuitem(text: String, block: CheckBox.() -> Unit = {}): CheckBox {
        val c = CheckBox(text)
        c.block()
        item(control = c)
        return c
    }

    private fun Column.checkmenuitem(text: String, block: CheckBox.() -> Unit = {}): CheckBox {
        val c = CheckBox(text)
        c.block()
        item(control = c)
        return c
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