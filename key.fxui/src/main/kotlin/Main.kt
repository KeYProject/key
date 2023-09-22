package io.github.wadoon.key

import de.uka.ilkd.key.control.DefaultUserInterfaceControl
import de.uka.ilkd.key.control.KeYEnvironment
import de.uka.ilkd.key.java.Services
import de.uka.ilkd.key.java.abstraction.KeYJavaType
import de.uka.ilkd.key.logic.Sequent
import de.uka.ilkd.key.logic.op.IObserverFunction
import de.uka.ilkd.key.macros.AutoMacro
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo
import de.uka.ilkd.key.pp.*
import de.uka.ilkd.key.proof.Goal
import de.uka.ilkd.key.proof.Node
import de.uka.ilkd.key.proof.Proof
import de.uka.ilkd.key.proof.ProofAggregate
import de.uka.ilkd.key.proof.init.IPersistablePO
import de.uka.ilkd.key.proof.init.ProblemInitializer
import de.uka.ilkd.key.proof.io.AbstractProblemLoader
import de.uka.ilkd.key.prover.TaskFinishedInfo
import de.uka.ilkd.key.prover.TaskStartedInfo
import de.uka.ilkd.key.settings.ProofIndependentSettings
import de.uka.ilkd.key.speclang.Contract
import de.uka.ilkd.key.util.KeYTypeUtil
import io.github.wadoon.key.controls.*
import io.github.wadoon.key.view.ProofTree
import io.github.wadoon.key.view.SetStatusBar
import io.github.wadoon.key.view.StatusBar
import javafx.application.Application
import javafx.beans.binding.Bindings
import javafx.beans.binding.ObjectBinding
import javafx.beans.property.SimpleMapProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.collections.FXCollections
import javafx.collections.MapChangeListener
import javafx.collections.ObservableList
import javafx.event.EventHandler
import javafx.geometry.Side
import javafx.scene.Parent
import javafx.scene.control.*
import javafx.scene.input.KeyCode
import javafx.scene.input.KeyCodeCombination
import javafx.scene.input.MouseButton
import javafx.scene.layout.BorderStrokeStyle
import javafx.scene.layout.Priority
import javafx.scene.paint.Color
import org.fxmisc.richtext.CharacterHit
import org.fxmisc.richtext.CodeArea
import org.key_project.util.collection.ImmutableSet
import org.kordamp.ikonli.Ikon
import org.kordamp.ikonli.fontawesome.FontAwesome
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.material2.Material2AL
import org.kordamp.ikonli.material2.Material2MZ
import org.scenicview.ScenicView
import tornadofx.*
import view.ExampleChooser
import view.chooseContract
import java.io.File
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import kotlin.io.path.isDirectory
import kotlin.io.path.isRegularFile
import kotlin.io.path.listDirectoryEntries


fun main(args: Array<String>) {
    Application.launch(KeyApp::class.java)
}

class KeyApp : App(KMainView::class)

class GlobalData : Component(), ScopedInstance {

    val workspacePathProperty = SimpleObjectProperty(Paths.get("."))
    var workspacePath by workspacePathProperty

    val selectedProofProperty = SimpleObjectProperty<Proof?>(null)
    var selectedProof: Proof? by selectedProofProperty

    val selectedNodeProperty = SimpleObjectProperty<Node?>(null)
    var selectedNode: Node? by selectedNodeProperty

    val selectedGoalProperty = SimpleObjectProperty<Goal?>(null)
    var selectedGoal: Goal? by selectedGoalProperty


    val openEnvironmentsProperty =
        SimpleMapProperty<Proof, KeYEnvironment<*>>(FXCollections.observableMap(IdentityHashMap()))
    val openEnvironments by openEnvironmentsProperty

    val selectedEnvironmentProperty = Bindings.valueAt(openEnvironmentsProperty, selectedProofProperty)
    val selectedEnvironment by selectedEnvironmentProperty

    val openProofsProperty: ObservableList<Proof> by lazy {
        val internal = FXCollections.observableArrayList<Proof>()
        val listener = MapChangeListener { c: MapChangeListener.Change<out Proof, out KeYEnvironment<*>> ->
            if (c.wasRemoved()) {
                internal.remove(c.key)
            }
            if (c.wasAdded()) {
                internal.addAll(c.key)
            }
        }
        openEnvironmentsProperty.addListener(listener)
        internal.asUnmodifiable()
    }

    val servicesProperty: ObjectBinding<Services?> =
        Bindings.createObjectBinding(
            { selectedProofProperty.value?.services },
            selectedProofProperty
        )
    val services: Services? by servicesProperty
}


//class GlobalDataModel(data: GlobalData = GlobalData()) : ItemViewModel<GlobalData>(data) {

class KMainView : View("KeY") {
    val globalData: GlobalData by inject()


    override val root = borderpane {
        top<TopView>()

        left = drawer(multiselect = true) {
            item(OpenProofs::class, expanded = true)
            item(ProofTree::class, expanded = true)
            item(StrategySettings::class)
        }


        center<CenterView>()

        bottom = vbox {
            drawer(Side.BOTTOM, multiselect = false, floatingContent = true) {
                item("Test", FontIcon(Material2AL.ALBUM), expanded = false, showHeader = true) {
                    add(Label("Only a test panel"))
                }
            }
            add(find<StatusBar>())
        }

        right = drawer(Side.RIGHT, multiselect = false) {
            item(SourceView::class)
        }
        /*  center = splitpane {
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
          }*/

        shortcut(KeyCodeCombination(KeyCode.F12)) { ScenicView.show(this) }
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
        listview<Proof>() {
            placeholder = Label("No proofs loaded")
            globalData.openProofsProperty.onChange {
                items.setAll(globalData.openProofsProperty)
            }

            selectionModel.selectedItemProperty().onChange {
                globalData.selectedProof = it
                globalData.selectedNode = null
                globalData.selectedGoal = null
            }

            globalData.selectedProofProperty.onChange {
                if (it != null)
                    selectionModel.select(it)
                else
                    selectionModel.clearSelection()
            }

            cellFormat {
                this.text = it.name().toString()
            }
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
            globalData.workspacePathProperty.onChange {
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
                            example?.let { loadFile(it) }
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
                    button("Auto", fontIcon = FontAwesome.PLAY_CIRCLE) {
                        action {
                            globalData.selectedProof?.let { proof ->
                                AutoMacro().applyTo(
                                    globalData.selectedEnvironment.ui,
                                    proof.root(), null, EventFireTaskListener
                                )
                            }
                        }

                        enableWhen(globalData.selectedProofProperty.isNotNull)
                    }
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

        if (loader.proof == null) {
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
                activateNewProof(env, proof)
            }
        } else {
            activateNewProof(env, loader.proof!!)
        }
    }

    private fun activateNewProof(env: KeYEnvironment<*>, proof: Proof) {
        globalData.openEnvironmentsProperty[proof] = env
        globalData.selectedProof = proof
        globalData.selectedGoal = proof.openGoals().head()
        globalData.selectedNode = proof.root()
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
    private val globalData: GlobalData by inject()
    private var currentGoal = SequentView()

    private val rootPane =
        //splitpane {
        tabpane {
            tab("Current Goal", currentGoal.root)
        }

    // }
    val components = FXCollections.observableArrayList<ObservableList<View>>()
    override val root: Parent = rootPane

    init {
        globalData.selectedGoalProperty.onChange {
            currentGoal.goal = it
            currentGoal.node = it?.node()
        }

        globalData.selectedNodeProperty.onChange {
            currentGoal.goal = globalData.selectedGoal
            currentGoal.node = it
        }
    }
}

class SequentView : Fragment("Current Sequent") {
    val globalData by inject<GlobalData>()

    private var positionTable: InitialPositionTable? = null
    val goalProperty = SimpleObjectProperty<Goal?>()
    var goal by goalProperty

    val nodeProperty = SimpleObjectProperty<Node?>()
    var node by nodeProperty

    val enableRuleProperty = goalProperty.isNotNull

    var menu: ContextMenu? = null

    val child: CodeArea = CodeArea().also {
        it.isEditable = false
        it.style {
            fontFamily = "monospace"
            fontSize = 14.pt
        }
    }
    override val root: Parent = child

    private var filter: IdentitySequentPrintFilter? = null

    private fun hightlightRange(start: Int, end: Int) {
        try {
            clearHighlight()
            child.selectRange(start, end)
            //child.setStyleClass(start, end, "sequent-highlight")
        } catch (_: IllegalStateException) {
        }
    }

    private fun clearHighlight() = child.clearStyle(0, child.getLength())

    init {
        child.onMouseMoved = EventHandler { evt ->
            positionTable?.let { pt ->

                val hit: CharacterHit = child.hit(evt.x, evt.y)
                val textPos = hit.insertionIndex
                try {
                    val pis: PosInSequent? = pt.getPosInSequent(textPos, filter)
                    if (pis != null) {
                        val r: Range = pt.rangeForIndex(textPos, child.length)
                        hightlightRange(r.start(), r.end())
                    } else {
                        hightlightRange(0, 0)
                    }
                } catch (npe: NullPointerException) {
                    npe.printStackTrace()
                }
                evt.consume()
            }

        }

        child.onMouseClicked = EventHandler { e ->
            e.consume()
            if (menu?.isShowing == true) menu?.hide()

            positionTable?.let { pt ->
                if (enableRuleProperty.value) {
                    val hit = child.hit(e.x, e.y)
                    val insertionPoint = hit.insertionIndex

                    val posInSequent = pt.getPosInSequent(insertionPoint, filter)
                    if (e.button == MouseButton.SECONDARY) {
                        posInSequent?.let { pis ->
                            menu = TacletContextMenu(pis, goal!!, globalData.selectedEnvironment).also {
                                it.show(child, e.screenX, e.screenY)
                            }
                        }
                    } else if (e.button == MouseButton.PRIMARY) {
                        menu =
                            ProofMacroMenu(goal!!.node(), posInSequent?.posInOccurrence, globalData.selectedEnvironment)
                                .also {
                                    it.show(child, e.screenX, e.screenY)
                                }
                    }
                }
            }
        }


        nodeProperty.onChange {
            if (it != null) {
                val services = it.proof().services
                val notationInfo = NotationInfo()
                val layouter = PosTableLayouter(80, 4, false)
                val sequent: Sequent = it.sequent()
                filter = IdentitySequentPrintFilter().also { it.setSequent(sequent) }

                ProofIndependentSettings.DEFAULT_INSTANCE.viewSettings.setUseUnicode(false)
                ProofIndependentSettings.DEFAULT_INSTANCE.viewSettings.setUsePretty(true)
                NotationInfo.DEFAULT_UNICODE_ENABLED = false
                NotationInfo.DEFAULT_PRETTY_SYNTAX = true
                notationInfo.refresh(services, true, false)

                val lp = LogicPrinter(notationInfo, services, layouter)
                lp.printSequent(sequent)
                val text = lp.result()
                positionTable = layouter.initialPositionTable
                child.clear()
                child.insertText(0, text)

                if (it.isClosed) {
                    child.style(false) {
                        borderColor = multi(box(Color.GREEN))
                        borderStyle = multi(BorderStrokeStyle.SOLID)
                    }
                    child.styleClass.setAll("closed-sequent-view")
                } else {
                    child.style(false) { }
                    child.styleClass.setAll("sequent-view")
                }
            } else {
                child.clear()
            }
        }
    }

}