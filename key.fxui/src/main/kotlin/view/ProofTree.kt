package io.github.wadoon.key.view

import de.uka.ilkd.key.proof.Node
import de.uka.ilkd.key.proof.Proof
import de.uka.ilkd.key.proof.ProofTreeEvent
import de.uka.ilkd.key.proof.ProofTreeListener
import javafx.application.Platform
import javafx.beans.Observable
import javafx.beans.property.*
import javafx.beans.value.ChangeListener
import javafx.beans.value.ObservableValue
import javafx.collections.FXCollections
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.*
import javafx.scene.control.cell.TextFieldTreeCell
import javafx.scene.input.ContextMenuEvent
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.material2.Material2AL
import org.kordamp.ikonli.material2.Material2RoundAL
import tornadofx.*
import java.util.*
import java.util.function.Consumer
import java.util.stream.Stream


class ProofTree : View("Proof Tree", FontIcon(Material2AL.ACCOUNT_TREE)) {
    private val services by property(null)
    private val proof: ObjectProperty<Proof> = SimpleObjectProperty()

    //private val root: ObjectProperty<Node?> = SimpleObjectProperty()
    private val sentinels: SetProperty<Node?> = SimpleSetProperty(FXCollections.observableSet<Any?>())
    private val colorOfNodes: MapProperty<Node, String> =
        SimpleMapProperty<Node, String>(FXCollections.observableHashMap<Node, String>())

    private var treeView: TreeView<TreeNode> by singleAssign()

    override val root = vbox {
        toolbar()
        treeView = treeview()
    }

    private var contextMenu: ContextMenu? = null
        get() {
            if (field == null) {
                field = ProofTreeContextMenu(this)
            }
            return field
        }


    private val deactivateRefreshProperty = property(false)
    private var deactivateRefresh by deactivateRefreshProperty

    private val proofTreeListener: ProofTreeListener = object : ProofTreeListener {
        override fun proofExpanded(proofTreeEvent: ProofTreeEvent?) {
            Platform.runLater { init() }
        }

        override fun proofIsBeingPruned(proofTreeEvent: ProofTreeEvent?) {}
        override fun proofPruned(proofTreeEvent: ProofTreeEvent?) {
            Platform.runLater { init() }
        }

        override fun proofStructureChanged(proofTreeEvent: ProofTreeEvent?) {
            Platform.runLater { init() }
        }

        override fun proofClosed(proofTreeEvent: ProofTreeEvent?) {
            Platform.runLater { init() }
        }

        override fun proofGoalRemoved(proofTreeEvent: ProofTreeEvent?) {
            Platform.runLater { init() }
        }

        override fun proofGoalsAdded(proofTreeEvent: ProofTreeEvent?) {
            Platform.runLater { init() }
        }

        override fun proofGoalsChanged(proofTreeEvent: ProofTreeEvent?) {
            Platform.runLater { init() }
        }

        override fun notesChanged(proofTreeEvent: ProofTreeEvent?) {}
    }
    private val treeCreation: ProofTree.TreeTransformationKey

    init {
        treeCreation = ProofTree.TreeTransformationKey()
        treeProof!!.setCellFactory { nodeTreeView: TreeView<TreeNode> ->
            cellFactory(
                nodeTreeView
            )
        }
        root.addListener { o: Observable? -> init() }
        proof.addListener(ChangeListener<Proof?> { prop: ObservableValue<out Proof?>?, old: Proof?, n: Proof? ->
            if (old != null) {
                old.removeProofTreeListener(proofTreeListener)
            }
            if (n != null) n.addProofTreeListener(proofTreeListener)
        })
        onContextMenuRequested = EventHandler { evt: ContextMenuEvent ->
            contextMenu!!.show(
                this,
                evt.screenX,
                evt.screenY
            )
        }
        init()
    }

    fun setNodeColor(n: Node, color: String) {
        colorOfNodes[n] = color
    }

    fun expandRootToSentinels() {
        if (getTreeProof()!!.root == null) {
            if (root.get() != null) {
                val item: TreeItem<TreeNode>
                item = if (sentinels.contains(root.get())) {
                    treeCreation.itemFactory(root.get())
                } else {
                    treeCreation.populate("Proof", root.get())
                }
                treeProof!!.setRoot(item)
            }
        }
        expandRootToLeaves(getTreeProof()!!.root)
    }

    fun getTreeProof(): TreeView<TreeNode>? {
        return treeProof
    }

    fun consumeNode(consumer: Consumer<Node?>, success: String?) {
        val item: TreeItem<TreeNode> = treeProof!!.getSelectionModel().selectedItem
        val n: Node = item.value.node
        if (n != null) {
            consumer.accept(n)
            Events.fire(PublishMessage(success))
        } else {
            Events.fire(PublishMessage("Current item does not have a node.", 2))
        }
    }

    private fun init() {}
    private fun cellFactory(nodeTreeView: TreeView<TreeNode>): TreeCell<TreeNode> {
        val tftc: TextFieldTreeCell<TreeNode> = TextFieldTreeCell<TreeNode>()
        val stringConverter: StringConverter<TreeNode> = object : StringConverter<TreeNode?>() {
            fun toString(`object`: TreeNode): String {
                return `object`.label
            }

            fun fromString(string: String?): TreeNode? {
                return null
            }
        }
        tftc.setConverter(stringConverter)
        tftc.itemProperty()
            .addListener(ChangeListener<TreeNode?> { p: ObservableValue<out TreeNode?>?, o: TreeNode?, n: TreeNode? ->
                if (n != null) repaint(
                    tftc
                )
            })
        return tftc
    }

    private fun repaint(tftc: TextFieldTreeCell<TreeNode>) {
        val item: TreeNode = tftc.item
        val n: Node = item.node
        tftc.style = ""
        if (n != null) {
            if (n.leaf() && !item.label.contains("CASE")) {
                if (n.isClosed) {
                    colorOfNodes.putIfAbsent(n, "lightseagreen")
                } else {
                    colorOfNodes.putIfAbsent(n, "indianred")
                }
                if (colorOfNodes.containsKey(n)) {
                    tftc.style = "-fx-background-color: " + colorOfNodes[n] + ";"
                }
            }
        }
        //TODO for Screenshot tftc.setStyle("-fx-font-size: 18pt");
        /* if (colorOfNodes.containsKey(n)) {
                tftc.setStyle("-fx-border-color: "+colorOfNodes.get(n)+";");
            }*/


        //System.out.println("colorOfNodes = " + colorOfNodes);
    }

    fun colorOfNodesProperty(): MapProperty<Node, String> {
        return colorOfNodes
    }

    fun getColorOfNodes(): ObservableMap<Node, String> {
        return colorOfNodes.get()
    }

    fun setColorOfNodes(colorOfNodes: ObservableMap<Node?, String?>) {
        this.colorOfNodes.set(colorOfNodes)
    }

    fun getRoot(): Node? {
        return root.get()
    }

    fun setRoot(root: Node?) {
        this.root.set(root)
    }

    fun rootProperty(): ObjectProperty<Node?> {
        return root
    }

    fun getProof(): Proof {
        return proof.get()
    }

    fun setProof(proof: Proof) {
        this.proof.set(proof)
    }

    fun proofProperty(): ObjectProperty<Proof> {
        return proof
    }

    fun getSentinels(): ObservableSet<Node?> {
        return sentinels.get()
    }

    fun setSentinels(sentinels: ObservableSet<Node?>?) {
        this.sentinels.set(sentinels)
    }

    fun sentinelsProperty(): SetProperty<Node?> {
        return sentinels
    }

    fun isDeactivateRefresh(): Boolean {
        return deactivateRefresh.get()
    }

    fun setDeactivateRefresh(deactivateRefresh: Boolean) {
        this.deactivateRefresh.set(deactivateRefresh)
    }

    fun deactivateRefreshProperty(): BooleanProperty {
        return deactivateRefresh
    }

    private fun populate(label: String, node: Node): TreeItem<TreeNode>? {
        return null
    }

    fun repopulate() {
        if (deactivateRefresh.get()) return
        if (root.get() != null) {
            val item: TreeItem<TreeNode> = treeCreation.create(proof.get())
            item.addEventHandler(
                TreeItem.branchExpandedEvent<Any>(),
                object : EventHandler<TreeItem.TreeModificationEvent<TreeNode?>?>() {
                    fun handle(event: TreeItem.TreeModificationEvent<TreeNode>) {
                        expandTreeView(event.treeItem)
                    }
                })
            item.addEventHandler(
                TreeItem.branchCollapsedEvent<Any>(),
                object : EventHandler<TreeItem.TreeModificationEvent<TreeNode?>?>() {
                    fun handle(event: TreeItem.TreeModificationEvent<TreeNode?>) {
                        collapseTreeView(event.treeItem)
                        treeProof!!.setCellFactory { nodeTreeView: TreeView<TreeNode> ->
                            cellFactory(
                                nodeTreeView
                            )
                        }
                    }
                })
            treeProof!!.setRoot(item)
            expandTreeView(item)
        }
        treeProof!!.refresh()
    }

    private fun expandTreeView(item: TreeItem<TreeNode>?) {
        if (item != null && !item.isLeaf) {
            item.setExpanded(true)
            for (child in item.getChildren()) {
                expandTreeView(child)
            }
        }
    }

    private fun collapseTreeView(item: TreeItem<TreeNode?>?) {
        if (item != null && !item.isLeaf) {
            item.setExpanded(false)
            for (child in item.getChildren()) {
                collapseTreeView(child)
            }
        }
    }

    @AllArgsConstructor
    private class TreeNode {
        var label: String? = null
        var node: Node? = null
    }

    internal open inner class TreeTransformationKey {
        fun create(proof: Proof): TreeItem<TreeNode> {
            val self1: TreeItem<TreeNode> = TreeItem<TreeNode>(TreeNode("Proof", null))
            self1.getChildren().add(populate("", proof.root()))
            return self1
        }

        protected fun itemFactory(n: Node, label: String): TreeItem<TreeNode> {
            return if (label == "") {
                itemFactory(n)
            } else {
                TreeItem<TreeNode>(TreeNode(label, n))
            }
        }

        protected fun itemFactory(n: Node): TreeItem<TreeNode> {
            return TreeItem<TreeNode>(TreeNode(n.serialNr() + ": " + toString(n), n))
        }

        protected fun toString(`object`: Node): String {
            return if (`object`.appliedRuleApp != null) {
                `object`.appliedRuleApp.rule().name().toString()
            } else {
                if (`object`.isClosed) "CLOSED GOAL" else "OPEN GOAL"
            }
        }

        /**
         * recursive population.
         *
         * @param label
         * @param n
         * @return
         */
        protected fun populate(label: String, n: Node): TreeItem<TreeNode> {
            //val treeNode = new TreeNode(label, n);
            val currentItem: TreeItem<TreeNode> = itemFactory(n, label)
            //new TreeItem<>(treeNode);

            // abort the traversing iff we have reached a sentinel!
            if (sentinels.contains(n)) {
                return currentItem
            }
            /* if (label.equals("Proof")) { //we are at the root
            TreeItem<TreeNode> self1 = new TreeItem<>(new TreeNode(n.serialNr() + ": " + toString(n), n));
             currentItem.getChildren().add(self1);
            }*/

            //if we are at a leaf we need to check goal state
            if (n.childrenCount() === 0) {
                //  TreeItem<TreeNode> e = new TreeItem<>(new TreeNode(
                //           n.isClosed() ? "CLOSED GOAL" : "OPEN GOAL", null));
                // currentItem.getChildren().addCell(e);
                return currentItem
            }
            assert(
                n.childrenCount() > 0 // there is at least one children
            )

            //consume child proof nodes until there are more than one child, then recursion!
            var node: Node = n.child(0)
            if (n.childrenCount() === 1) {
                currentItem.getChildren().add(
                    TreeItem<TreeNode>(
                        TreeNode(
                            node.serialNr() + ": " + toString(node),
                            node
                        )
                    )
                )
                while (node.childrenCount() === 1) {
                    node = node.child(0)
                    currentItem.getChildren().add(
                        TreeItem<TreeNode>(
                            TreeNode(
                                node.serialNr() + ": " + toString(node),
                                node
                            )
                        )
                    )
                }


                /*do {
                    currentItem.getChildren().add(itemFactory(node));
                    node = node.child(0);
                } while (node.childrenCount() == 1);*/
            }

            // if the current node has more zero children. abort.
            if (node.childrenCount() === 0) return currentItem
            assert(
                node.childrenCount() > 0 // there is at least 2 children
            )
            val nodeIterator: Iterator<Node> = node.childrenIterator()
            var branchCounter = 1
            while (nodeIterator.hasNext()) {
                val childNode: Node = nodeIterator.next()
                if (childNode.nodeInfo.branchLabel != null) {
                    val populate: TreeItem<TreeNode> =
                        populate(childNode.nodeInfo.branchLabel, childNode)
                    currentItem.getChildren().add(populate)
                } else {
                    val populate: TreeItem<TreeNode> = populate("CASE $branchCounter", childNode)
                    //TreeItem<TreeNode> self = new TreeItem<>(new TreeNode(childNode.serialNr() + ": " + toString(childNode), childNode));
                    val self: TreeItem<TreeNode> = itemFactory(childNode)
                    populate.getChildren().add(0, self)
                    currentItem.getChildren().add(populate)
                    branchCounter++
                }
            }
            return currentItem
        }
    }

    @RequiredArgsConstructor
    internal inner class TreeTransformationScript : ProofTree.TreeTransformationKey() {
        private val manager: ProofTreeManager<KeyData>? = null

        /**
         * maps a node to its siblings, that were created by an mutator call.
         */
        private var entryExitMap: Multimap<Node, Node> = HashMultimap.create()

        /**
         * maps a node to its mutator, that was applied on it.
         */
        private var mutatedBy: MutableMap<Node, ASTNode> = HashMap<Node, ASTNode>()
        override fun create(proof: Proof?): TreeItem<TreeNode> {
            val nodes: Set<PTreeNode<KeyData>> = manager.getNodes()
            entryExitMap.clear()
            mutatedBy.clear()
            nodes.forEach(
                Consumer<PTreeNode<KeyData?>> { pn: PTreeNode<KeyData?> ->
                    try {
                        if (pn.isAtomic()) {
                            val startNode: Node = pn.getStateBeforeStmt().getSelectedGoalNode().getData().getNode()
                            mutatedBy[startNode] = pn.getStatement()
                            pn.getMutatedNodes().forEach { mn -> entryExitMap.put(startNode, mn.getData().getNode()) }
                        }
                    } catch (e: NullPointerException) {
                    }
                }
            )
            return super.create(proof)
        }

        protected override fun populate(label: String?, n: Node): TreeItem<TreeNode> {
            val currentItem: `val` = itemFactory(n)
            for (child in entryExitMap.get(n)) {
                if (isMutated(child)) {
                    currentItem.getChildren().add(populate("", child))
                } else {
                    currentItem.getChildren().add(super.itemFactory(child))
                }
            }
            return currentItem
        }

        private fun isMutated(child: Node): Boolean {
            return mutatedBy.containsKey(child)
        }

        override fun itemFactory(n: Node): TreeItem<TreeNode> {
            val ast: ASTNode? = mutatedBy[n]
            var lbl = ast.accept(ShortCommandPrinter()) as String
            lbl += ("  " + n.serialNr()).toString() + " " + toString(n)
            return TreeItem<TreeNode>(TreeNode(lbl, n))
        }

        //TODO: Reverse ArrayList in the end or nah?
        @Deprecated("")
        fun getBranchLabels(node: TreeNode?): ArrayList<String> {
            val proofTree: TreeItem<TreeNode> = create(proof.get())
            val branchlabels = ArrayList<String>()
            var i = 0
            branchlabels[0] = node.label
            while (node != null) {
                if (branchlabels[i] != node.label) {
                    i++
                    branchlabels[i] = node.label
                }
                //TODO: node = node.parent
            }
            return branchlabels
        }

        fun getBranchLabels(node: Node): ArrayList<String> {
            val branchlabels = ArrayList<String>()
            var i = 0
            //TODO: branchlabel = all branchlabels or only next one
            branchlabels[0] = node.nodeInfo.branchLabel
            var n: Node = node.parent()
            while (n != null) {
                if (branchlabels[i] != n.nodeInfo.branchLabel) {
                    i++
                    branchlabels[i] = n.nodeInfo.branchLabel
                }
                n = n.parent()
            }
            return branchlabels
        }
    }

    companion object {
        /**
         * From https://www.programcreek.com/java-api-examples/index.php?api=javafx.scene.control.TreeItem
         *
         * @param candidate
         */
        private fun expandRootToItem(candidate: TreeItem<TreeNode>?) {
            if (candidate != null) {
                expandRootToItem(candidate.parent)
                if (!candidate.isLeaf) {
                    candidate.setExpanded(true)
                }
            }
        }

        fun expandRootToLeaves(candidate: TreeItem<*>?) {
            if (candidate != null) {
                if (!candidate.isLeaf) {
                    candidate.setExpanded(true)
                    val children: ObservableList<TreeItem<*>> = candidate.getChildren()
                    children.forEach { treeItem -> expandRootToLeaves(treeItem) }
                }
            }
        }
    }


    fun createProofTreeContextMenu(proofTree: ProofTree): ContextMenu = contextmenu() {
        item("Refresh", graphic = FontIcon(Material2RoundAL.REFRESH)) {
            proofTree.repopulate()
        }

        item("Show Sequent")

        item("Show in Goal List")

        item("Expand Tree")

        isAutoFix = true
        isAutoHide = true
    }

    private fun onCreateCases(evt: ActionEvent?) {
        if (proofTree.getProof() == null) {
            return
        }
        val labels: List<Array<String>> = LabelFactory.getLabelOfOpenGoals(
            proofTree.getProof(),
            LabelFactory::getBranchingLabel
        )
        val text: String
        text = if (labels.isEmpty()) {
            "// no open goals"
        } else if (labels.size == 1) {
            "// only one goal"
        } else {
            var upperLimit = 0
            /* trying to find the common suffix*/try {
                val ref = labels[0]
                while (true) {
                    for (lbl in labels) {
                        if (lbl[upperLimit] != ref[upperLimit]) {
                            break
                        }
                    }
                    upperLimit++
                    upperLimit++
                }
            } catch (e: ArrayIndexOutOfBoundsException) {
            }
            val finalUpperLimit = upperLimit
            labels.stream()
                .map<Stream<String>> { a: Array<String> ->
                    Arrays.stream<String>(
                        a,
                        finalUpperLimit,
                        a.size
                    )
                }
                .map<String> { s: Stream<String> ->
                    s.reduce { a: String, b: String -> (b + LabelFactory.SEPARATOR).toString() + a }
                        .orElse("error")
                }
                .map<String> { s: String? ->
                    String.format(
                        "\tcase match \"%s\" :\n\t\t//commands",
                        s
                    )
                }
                .reduce { a: String, b: String ->
                    """
                         $a
                         $b
                         """.trimIndent()
                }
                .orElse("ERROR")
        }
        val s = "cases {\n$text\n}"
        Events.fire(InsertAtTheEndOfMainScript(s))
        Events.fire(PublishMessage("Copied to Clipboard"))
    }
}
}


class ProofTreeContextMenu(private val proofTree: ProofTree) : ContextMenu() {
    private var copyBranchLabel = MenuItem("Branch Label")
    private var copyProgramLines = MenuItem("Program Lines")
    private var createCases = MenuItem("Created Case for Open Goals")
    private var refresh = MenuItem("Refresh")
    private var showSequent = MenuItem("Show Sequent")
    private var showGoal = MenuItem("Show in Goal List")
    private var expandAllNodes = MenuItem("Expand Tree")

    init {
        refresh.onAction = EventHandler<ActionEvent> { event: ActionEvent? -> proofTree.repopulate() }
        refresh.graphic = MaterialDesignIconView(MaterialDesignIcon.REFRESH)
        copyBranchLabel.onAction = EventHandler<ActionEvent> { evt: ActionEvent? ->
            proofTree.consumeNode({ n ->
                Utils.intoClipboard(
                    LabelFactory.getBranchingLabel(n)
                )
            }, "Copied!")
        }
        copyProgramLines.onAction = EventHandler<ActionEvent> { evt: ActionEvent? ->
            proofTree.consumeNode({ n ->
                Utils.intoClipboard(
                    LabelFactory.getProgramLines(n)
                )
            }, "Copied!")
        }
        val copySequent = MenuItem("Sequent")
        copySequent.onAction = EventHandler<ActionEvent> { evt: ActionEvent? ->
            proofTree.consumeNode({ n ->
                assert(proofTree.getServices() != null) { "set KeY services!" }
                val s: String = LogicPrinter.quickPrintSequent(n.sequent(), proofTree.getServices())
                Utils.intoClipboard(s)
            }, "Copied!")
        }
        val copyRulesLabel = MenuItem("Rule labels")
        copyRulesLabel.onAction = EventHandler<ActionEvent> { evt: ActionEvent? ->
            proofTree.consumeNode({ n ->
                Utils.intoClipboard(
                    LabelFactory.getRuleLabel(n)
                )
            }, "Copied!")
        }
        val copyProgramStatements = MenuItem("Statements")
        copyProgramStatements.onAction = EventHandler<ActionEvent> { event: ActionEvent? ->
            proofTree.consumeNode({ n ->
                Utils.intoClipboard(
                    LabelFactory.getProgramStatmentLabel(n)
                )
            }, "Copied!")
        }
        val copy = Menu(
            "Copy", MaterialDesignIconView(MaterialDesignIcon.CONTENT_COPY),
            copyBranchLabel, copyProgramLines,
            copyProgramStatements, copyRulesLabel,
            copySequent
        )
        createCases.onAction = EventHandler { evt: ActionEvent? ->
            onCreateCases(
                evt
            )
        }
        showSequent.onAction = EventHandler<ActionEvent> { evt: ActionEvent? ->
            proofTree.consumeNode(
                { n -> Events.fire(ShowSequent(n)) },
                ""
            )
        }
        showGoal.onAction = EventHandler<ActionEvent> { evt: ActionEvent? ->
            proofTree.consumeNode(
                { n -> Events.fire(SelectNodeInGoalList(n)) },
                "Found!"
            )
        }
        expandAllNodes.onAction = EventHandler<ActionEvent> { event: ActionEvent? ->
            proofTree.expandRootToLeaves(
                proofTree.getTreeProof().getRoot()
            )
        }
        items.setAll(refresh, expandAllNodes, SeparatorMenuItem(), copy, createCases, showSequent, showGoal)
        isAutoFix = true
        isAutoHide = true
    }

    private fun onCreateCases(evt: ActionEvent?) {
        if (proofTree.getProof() == null) {
            return
        }
        val labels: List<Array<String>> = LabelFactory.getLabelOfOpenGoals(
            proofTree.getProof(),
            LabelFactory::getBranchingLabel
        )
        val text: String
        text = if (labels.isEmpty()) {
            "// no open goals"
        } else if (labels.size == 1) {
            "// only one goal"
        } else {
            var upperLimit = 0
            /* trying to find the common suffix*/try {
                val ref = labels[0]
                while (true) {
                    for (lbl in labels) {
                        if (lbl[upperLimit] != ref[upperLimit]) {
                            break
                        }
                    }
                    upperLimit++
                    upperLimit++
                }
            } catch (e: ArrayIndexOutOfBoundsException) {
            }
            val finalUpperLimit = upperLimit
            labels.stream()
                .map<Stream<String>> { a: Array<String> ->
                    Arrays.stream<String>(
                        a,
                        finalUpperLimit,
                        a.size
                    )
                }
                .map<String> { s: Stream<String> ->
                    s.reduce { a: String, b: String -> (b + LabelFactory.SEPARATOR).toString() + a }
                        .orElse("error")
                }
                .map<String> { s: String? ->
                    String.format(
                        "\tcase match \"%s\" :\n\t\t//commands",
                        s
                    )
                }
                .reduce { a: String, b: String ->
                    """
                         $a
                         $b
                         """.trimIndent()
                }
                .orElse("ERROR")
        }
        val s = "cases {\n$text\n}"
        Events.fire(InsertAtTheEndOfMainScript(s))
        Events.fire(PublishMessage("Copied to Clipboard"))
    }
}