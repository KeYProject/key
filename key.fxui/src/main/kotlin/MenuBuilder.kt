package io.github.wadoon.key

import de.uka.ilkd.key.control.KeYEnvironment
import de.uka.ilkd.key.control.ProofControl
import de.uka.ilkd.key.logic.Name
import de.uka.ilkd.key.logic.PosInOccurrence
import de.uka.ilkd.key.logic.SequentFormula
import de.uka.ilkd.key.logic.Term
import de.uka.ilkd.key.macros.ProofMacro
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand
import de.uka.ilkd.key.pp.NotationInfo
import de.uka.ilkd.key.pp.PosInSequent
import de.uka.ilkd.key.proof.Goal
import de.uka.ilkd.key.proof.Node
import de.uka.ilkd.key.prover.ProverTaskListener
import de.uka.ilkd.key.prover.TaskFinishedInfo
import de.uka.ilkd.key.prover.TaskStartedInfo
import de.uka.ilkd.key.rule.BuiltInRule
import de.uka.ilkd.key.rule.RewriteTaclet
import de.uka.ilkd.key.rule.TacletApp
import io.github.wadoon.key.view.SetStatusBar
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.*
import javafx.scene.input.Clipboard
import javafx.scene.input.ClipboardContent
import javafx.scene.paint.Color
import javafx.scene.text.Text
import org.key_project.util.collection.ImmutableList
import org.key_project.util.collection.ImmutableSLList
import org.key_project.util.reflection.ClassLoaderUtil
import org.slf4j.LoggerFactory
import tornadofx.FX
import tornadofx.action
import tornadofx.item
import java.util.*
import java.util.stream.Collectors

object EventFireTaskListener : ProverTaskListener {
    override fun taskStarted(info: TaskStartedInfo?) {
        FX.eventbus.fire(SetStatusBar("Task started: ${info.toString()}"))
    }

    override fun taskProgress(position: Int) {
        FX.eventbus.fire(SetStatusBar("Task progress: ${position}"))
    }

    override fun taskFinished(info: TaskFinishedInfo?) {
        FX.eventbus.fire(SetStatusBar("Task finished: ${info.toString()}"))
    }
}


class TacletContextMenu(private val pos: PosInSequent, private val goal: Goal, val env: KeYEnvironment<*>) :
    ContextMenu() {

    private val CLUTTER_RULESETS = setOf(
        Name("notHumanReadable"),
        Name("obsolete"),
        Name("pullOutQuantifierAll"),
        Name("pullOutQuantifierEx")
    )
    private val CLUTTER_RULES = setOf(
        Name("cut_direct_r"), Name("cut_direct_l"),
        Name("case_distinction_r"),
        Name("case_distinction_l"),
        Name("local_cut"),
        Name("commute_and_2"),
        Name("commute_or_2"),
        Name("boxToDiamond"),
        Name("pullOut"),
        Name("typeStatic"),
        Name("less_is_total"),
        Name("less_zero_is_total"),
        Name("applyEqReverse"),
        Name("eqTermCut"),
        Name("instAll"),
        Name("instEx"),
    )
    private val FILTER_SCRIPT_COMMANDS = setOf("exit", "leave", "javascript", "skip", "macro", "rule", "script")

    private val occ = pos.posInOccurrence

    private val control: ProofControl = env.ui.getProofControl().also {
        it.setMinimizeInteraction(true)
    }

    private val builtInRules = control.getBuiltInRule(goal, occ)


    private val noRules = item("No rules found")
    private val moreRules: Menu = Menu()
    private val insertHidden: Menu = Menu()
    private val scriptCommands: Menu = Menu()

    private val copyToClipboard = item("Copy to clipboard") {
        action { handleCopyToClipboard() }
    }

    private val createAbbr = item("Create abbreviation") {

    }
    private val enableAbbr = item("Enable abbreviation")
    private val disableAbbr = item("Disable abbreviation")
    private val changeAbbr = item("Change abbreviation")

    private val notationInfo = NotationInfo()

    init {
        isAutoFix = true
        isAutoHide = true

        try {
            //createMacroMenu(KeYApi.getScriptCommandApi().scriptCommands, KeYApi.getMacroApi().macros)
            val findTaclet = control.getFindTaclet(goal, occ)
            createTacletMenu(
                removeRewrites(findTaclet)
                    .prepend(control.getRewriteTaclet(goal, occ)),
                control.getNoFindTaclet(goal), builtInRules
            )
        } catch (e: NullPointerException) {
            createDummyMenuItem()
        }
    }

    private fun createMacroMenu(scriptCommandList: Collection<ProofScriptCommand<*>>, macros: Collection<ProofMacro>) {
        for (macro in macros) {
            val item = MenuItem(macro.getScriptCommandName())
            item.onAction = EventHandler {
                handleMacroCommandApplication(
                    macro
                )
            }
            scriptCommands.items.add(item)
        }
        for (com in scriptCommandList) {
            if (!FILTER_SCRIPT_COMMANDS.contains(com.getName())) {
                val item = MenuItem(com.getName())
                item.onAction = EventHandler {
                    handleCommandApplication(
                        com
                    )
                }
                scriptCommands.items.add(item)
            }
        }
        //        rootMenu.getItems().add(scriptCommands);
    }

    /**
     * Creates the menu by adding all submenus and items.
     */
    private fun createTacletMenu(
        find: ImmutableList<TacletApp>,
        noFind: ImmutableList<TacletApp>,
        builtInList: ImmutableList<BuiltInRule>
    ) {
        val findTaclets = find.stream().collect(Collectors.toList())
        val noFindTaclets = noFind.stream().collect(Collectors.toList())
        Collections.sort(
            findTaclets,  //compare by name
            Comparator.comparing { it.taclet().name() }
        )
        val toAdd: MutableList<TacletApp> = ArrayList(findTaclets.size + noFindTaclets.size)
        toAdd.addAll(findTaclets)
        var rulesAvailable = find.size() > 0

        //remove all cut rules from menu and add cut command for that
        if (pos.isSequent) {
            rulesAvailable = rulesAvailable or (noFind.size() > 0)
            toAdd.addAll(replaceCutOccurrence(noFindTaclets))
        }



        if (rulesAvailable) {
            createMenuItems(toAdd)
        } else {
            noRules.isVisible = true
        }
        if (occ != null) createAbbrevSection(pos.posInOccurrence.subTerm())
    }

    private fun replaceCutOccurrence(findTaclets: List<TacletApp>): List<TacletApp> {
        val toReturn: MutableList<TacletApp> = ArrayList()
        for (i in findTaclets.indices) {
            val tacletApp = findTaclets[i]
            if (!tacletApp.rule().displayName().startsWith("cut")) {
                toReturn.add(tacletApp)
            }
        }
        return toReturn
    }

    private fun createDummyMenuItem() {
        val t = Text("This is not a goal state.\nSelect a goal state from the list.")
        t.fill = Color.RED
        val item = MenuItem()
        item.graphic = t
        items.add(0, item)
    }

    /**
     * Creates menu items for all given taclets. A submenu for insertion of
     * hidden terms will be created if there are any, and rare rules will be in
     * a 'More rules' submenu.
     *
     * @param taclets the list of taclets to create menu items for
     */
    private fun createMenuItems(taclets: List<TacletApp>) {
        var idx = 0
        for (app in taclets) {
            val taclet = app.taclet()
            val item = MenuItem(app.taclet().displayName().toString())
            item.onAction = EventHandler { goal.apply(app) }
            run {
                // If one of the sets contains the rule it is considered rare
                // and moved to a 'More rules' submenu.
                var rareRule = false
                for (rs in taclet.ruleSets) {
                    if (CLUTTER_RULESETS.contains(rs.name())) rareRule = true
                }
                if (CLUTTER_RULES.contains(taclet.name())) rareRule = true
                if (rareRule) moreRules.items.add(item) else items.add(idx++, item)
            }
        }
        if (moreRules.items.size > 0) moreRules.isVisible = true
    }

    /**
     * Manages the visibility of all menu items dealing with abbreviations based
     * on if the given term already is abbreviated and if the abbreviation is
     * enabled.
     *
     * @param t the term to check if there already is an abbreviation of
     */
    private fun createAbbrevSection(t: Term) {
        val scm = notationInfo.abbrevMap
        if (scm.containsTerm(t)) {
            changeAbbr.isVisible = true
            if (scm.isEnabled(t)) {
                disableAbbr.isVisible = true
            } else {
                enableAbbr.isVisible = true
            }
        } else {
            createAbbr.isVisible = true
        }
    }

    /**
     * Handles the application of an 'ordinary' rule.
     *
     * @param event
     */
    private fun handleRuleApplication(event: TacletApp) {
        // Synchronization for StaticSequentView
        /*   parentController.setLastTacletActionID(parentController.getOwnID());
        mediator.getUI().getProofControl().selectedTaclet(
                ((TacletMenuItem) event.getSource()).getTaclet(), goal,
                pos.getPosInOccurrence());*/

        //System.out.println("event = [" + event + "]");
    }

    private fun handleCommandApplication(event: ProofScriptCommand<*>) {
        //Events.fire(CommandApplicationEvent(event, pos.posInOccurrence, goal))
    }

    private fun handleMacroCommandApplication(event: ProofMacro) {
        event.applyTo(env.ui, goal.node(), occ, EventFireTaskListener)
    }

    /**
     * Handles rule application for automode.
     *
     * @param event
     */
    private fun handleFocussedRuleApplication(event: ActionEvent) {
        // Synchronization for StaticSequentView
        // parentController.setLastTacletActionID(parentController.getOwnID());
        //mediator.getUI().getProofControl()
//                .startFocussedAutoMode(pos.getPosInOccurrence(), goal);
    }

    /**
     * Handles action of the 'Copy to clipboard' menu item.
     */
    private fun handleCopyToClipboard() {
        val clipboard = Clipboard.getSystemClipboard()
        val content = ClipboardContent()
        val term: Term = pos.posInOccurrence.subTerm()
        val g = goal
        val termString: String = term.toString()//Utils.printParsableTerm(term, goal)
        content.putString(termString)
        clipboard.setContent(content)
    }

    /**
     * Checks whether a string is a valid term abbreviation (is not empty and
     * only contains 0-9, a-z, A-Z and underscore (_)).
     *
     * @param s the string to check
     * @return true iff the string is a valid term abbreviation
     */
    private fun validateAbbreviation(s: String?): Boolean {
        if (s == null || s.length == 0) return false
        for (i in 0 until s.length) {
            if (!(s[i] <= '9' && s[i] >= '0' || s[i] <= 'z' && s[i] >= 'a' || s[i] <= 'Z' && s[i] >= 'A' || s[i] == '_')) return false
        }
        return true
    }

    /**
     * Handles the creation of a term abbreviation.
     *
     * @param event
     */
    private fun handleCreateAbbreviation(event: ActionEvent) {
        if (occ!!.posInTerm() != null) {
            val oldTerm = occ.subTerm().toString()
            val term = if (oldTerm.length > 200) oldTerm.substring(0, 200) else oldTerm
            abbreviationDialog(
                "Create Abbreviation",
                "Enter abbreviation for term: \n$term\n", null
            )
        }
    }

    /**
     * Handles the change of a term abbreviation.
     *
     * @param event
     */
    private fun handleChangeAbbreviation(event: ActionEvent) {
        if (occ!!.posInTerm() != null) {
            abbreviationDialog(
                "Change Abbreviation", """
     Enter abbreviation for term: 
     ${occ.subTerm()}
     """.trimIndent(),
                notationInfo.abbrevMap.getAbbrev(occ.subTerm()).substring(1)
            )
        }
    }

    /**
     * Opens a dialog that requires the input of a term abbreviation and iff a
     * valid abbreviation is given applies it.
     *
     * @param header    the header text for the dialog
     * @param message   the message of the dialog
     * @param inputText preset text for the input line. Can be used to pass an already
     * existing abbreviation to change.
     */
    private fun abbreviationDialog(
        header: String, message: String,
        inputText: String?
    ) {
        val dialog = TextInputDialog(inputText)

        // Get the Stage and addCell KeY Icon.
        /* Stage stage = (Stage) dialog.getDialogPane().getScene().getWindow();
        stage.getIcons()
                .addCell(new Image(NUIConstants.KEY_APPLICATION_WINDOW_ICON_PATH));
        dialog.setTitle("Abbreviation Dialog");
        dialog.setHeaderText(header);
        dialog.setContentText(message);
        Optional<String> result = dialog.showAndWait();
        result.ifPresent(abbreviation -> {
            if (abbreviation != null) {
                if (!validateAbbreviation(abbreviation)) {
                    getMainApp().showAlert("Sorry", null,
                            "Only letters, numbers and '_' are allowed for Abbreviations",
                            AlertType.INFORMATION);
                } else {
                    try {
                        AbbrevMap abbrevMap = mediator.getNotationInfo()
                                .getAbbrevMap();
                        if (abbrevMap.containsTerm(occ.subTerm()))
                            abbrevMap.changeAbbrev(occ.subTerm(), abbreviation);
                        else
                            abbrevMap.put(occ.subTerm(), abbreviation, true);
                        parentController.forceRefresh();
                    } catch (Exception e) {
                        getMainApp().showAlert("Sorry",
                                "Something has gone wrong.", e.getMessage(),
                                AlertType.ERROR);
                    }
                }
            }
        });*/
    }

    /**
     * Handles the enable of a term abbreviation.
     *
     * @param event
     */
    private fun handleEnableAbbreviation(event: ActionEvent) {
        if (occ!!.posInTerm() != null) {
            notationInfo.abbrevMap.setEnabled(occ.subTerm(), true)
            //   parentController.forceRefresh();
        }
    }

    /**
     * Handles the disable of a term abbreviation.
     *
     * @param event
     */
    private fun handleDisableAbbreviation(event: ActionEvent) {
        if (occ!!.posInTerm() != null) {
            notationInfo.abbrevMap.setEnabled(occ.subTerm(), false)
            //  parentController.forceRefresh();
        }
    }

    companion object {
        private val CLUTTER_RULESETS: MutableSet<Name> = LinkedHashSet()
        private val CLUTTER_RULES: MutableSet<Name> = LinkedHashSet()
        private val FILTER_SCRIPT_COMMANDS: MutableSet<String> = LinkedHashSet()

        init {
            CLUTTER_RULESETS.add(Name("notHumanReadable"))
            CLUTTER_RULESETS.add(Name("obsolete"))
            CLUTTER_RULESETS.add(Name("pullOutQuantifierAll"))
            CLUTTER_RULESETS.add(Name("pullOutQuantifierEx"))
        }

        init {
            FILTER_SCRIPT_COMMANDS.add("exit")
            FILTER_SCRIPT_COMMANDS.add("leave")
            FILTER_SCRIPT_COMMANDS.add("javascript")
            FILTER_SCRIPT_COMMANDS.add("skip")
            FILTER_SCRIPT_COMMANDS.add("macro")
            FILTER_SCRIPT_COMMANDS.add("rule")
            FILTER_SCRIPT_COMMANDS.add("script")
        }

        init {
            CLUTTER_RULES.add(Name("cut_direct_r"))
            CLUTTER_RULES.add(Name("cut_direct_l"))
            CLUTTER_RULES.add(Name("case_distinction_r"))
            CLUTTER_RULES.add(Name("case_distinction_l"))
            CLUTTER_RULES.add(Name("local_cut"))
            CLUTTER_RULES.add(Name("commute_and_2"))
            CLUTTER_RULES.add(Name("commute_or_2"))
            CLUTTER_RULES.add(Name("boxToDiamond"))
            CLUTTER_RULES.add(Name("pullOut"))
            CLUTTER_RULES.add(Name("typeStatic"))
            CLUTTER_RULES.add(Name("less_is_total"))
            CLUTTER_RULES.add(Name("less_zero_is_total"))
            CLUTTER_RULES.add(Name("applyEqReverse"))

            // the following are used for drag'n'drop interactions
            CLUTTER_RULES.add(Name("eqTermCut"))
            CLUTTER_RULES.add(Name("instAll"))
            CLUTTER_RULES.add(Name("instEx"))
        }

        /**
         * Removes RewriteTaclet from the list.
         *
         * @param list the IList<Taclet> from where the RewriteTaclet are removed
         * @return list without RewriteTaclets
        </Taclet> */
        private fun removeRewrites(
            list: ImmutableList<TacletApp>
        ): ImmutableList<TacletApp> {
            // return list;
            var result: ImmutableList<TacletApp> = ImmutableSLList.nil()
            val it: Iterator<TacletApp> = list.iterator()
            while (it.hasNext()) {
                val tacletApp = it.next()
                val taclet = tacletApp.taclet()
                result = if (taclet is RewriteTaclet) result else result.prepend(tacletApp)
            }
            return result
        }
    }

    val LOGGER = LoggerFactory.getLogger(TacletContextMenu::class.java)

    fun handle(app: TacletApp, pio: PosInOccurrence, g: Goal) {
        LOGGER.debug("Handling {}", app)

        val tapName: String = app.taclet().name().toString()
        val seqForm: SequentFormula = pio.sequentFormula()

    }
}


fun ProofMacroMenu(node: Node, posInOcc: PosInOccurrence?, env: KeYEnvironment<*>): ContextMenu {
    val REGISTERED_MACROS = ClassLoaderUtil.loadServices(ProofMacro::class.java)

    // Macros are grouped according to their category.
    val submenus = REGISTERED_MACROS.filter { it.canApplyTo(node, posInOcc) }.groupBy { it.category }

    var first = true
    val items = arrayListOf<MenuItem>()
    for ((cat, macros) in submenus) {
        if (!first) items.add(SeparatorMenuItem())
        first = false
        for (macro in macros)
            items.add(MenuItem(macro.getName()).also {
                it.setOnAction { env.proofControl.runMacro(node, macro, posInOcc) }
            })
    }

    return ContextMenu().also {
        it.items.setAll(items)
        it.isAutoFix = true
        it.isAutoHide = true
    }
}

