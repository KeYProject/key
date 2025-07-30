/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionEvent;
import java.util.*;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofMacroMenu;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.useractions.FocussedAutoModeUserAction;
import de.uka.ilkd.key.gui.join.JoinMenuItem;
import de.uka.ilkd.key.gui.mergerule.MergeRuleMenuItem;
import de.uka.ilkd.key.gui.prooftree.ProofTreePopupFactory;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.join.JoinIsApplicable;
import de.uka.ilkd.key.proof.join.ProspectivePartner;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.FeatureSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverTypeCollection;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.StringUtil;

import org.jspecify.annotations.NonNull;

/**
 * The menu shown by a {@link CurrentGoalViewListener} when the user clicks on a
 * {@link CurrentGoalView}, i.e. when the user clicks on the sequent.
 * <p>
 * Shows all {@link Taclet}s that are applicable at a selected position.
 */
public final class CurrentGoalViewMenu extends SequentViewMenu<CurrentGoalView> {
    private static final String INTRODUCE_AXIOM_TACLET_NAME = "introduceAxiom";

    private static final String MORE_RULES = "More rules";
    private static final String APPLY_CONTRACT = "Apply Contract";
    private static final String CHOOSE_AND_APPLY_CONTRACT = "Choose and Apply Contract...";
    private static final String ENTER_LOOP_SPECIFICATION = "Enter Loop Specification...";
    private static final String APPLY_RULE = "Apply Rule";
    private static final String NO_RULES_APPLICABLE = "No rules applicable.";

    private Set<String> clutterRuleSets;
    private Set<String> clutterRules;

    public static final int TOO_MANY_TACLETS_THRESHOLD = 15; // reduce for debugging.

    private KeYMediator mediator;
    private final TacletAppComparator comp = new TacletAppComparator();
    private final Action actionCreateAbbreviation = new CreateAbbreviationAction();
    private final Action actionDisableAbbreviation = new DisableAbbreviationAction();
    private final Action actionEnableAbbreviation = new EnableAbbreviationAction();
    private final Action actionChangeAbbreviation = new ChangeAbbreviationAction();
    private final KeyAction actionFocussedAutoMode = new FocussedRuleApplicationAction();
    private final Comparator<? super TacletApp> sortTacletByName =
        Comparator.comparing(it -> it.taclet().displayName());


    /**
     * Creates an empty menu.
     */
    CurrentGoalViewMenu() {
        initClutterRules();
    }

    /**
     * Creates a new menu that displays all applicable actions and rules at the given position
     *
     * @param sequentView the SequentView that is the parent of this menu
     * @param findList with all applicable FindTaclets
     * @param rewriteList with all applicable RewriteTaclets
     * @param noFindList with all applicable noFindTaclets
     * @param builtInList with all applicable BuiltInRules
     * @param pos the PosInSequent
     */
    CurrentGoalViewMenu(CurrentGoalView sequentView, ImmutableList<TacletApp> findList,
            ImmutableList<TacletApp> rewriteList, ImmutableList<TacletApp> noFindList,
            ImmutableList<BuiltInRule> builtInList, PosInSequent pos) {
        super(sequentView, pos);
        this.mediator = sequentView.getMediator();

        initClutterRules();

        // delete RewriteTaclet from findList because they will be in
        // the rewrite list and concatenate both lists
        createMenu(removeRewrites(findList).prepend(rewriteList),
            removeIntroduceAxiomTaclet(noFindList), builtInList);
    }

    /**
     * Removes the unsound "introduceAxiom" taclet from the list of displayed taclets.
     *
     * @param list The list from which to filter.
     * @return The original list, without the "introduceAxiom" taclet.
     */
    private static ImmutableList<TacletApp> removeIntroduceAxiomTaclet(
            ImmutableList<TacletApp> list) {
        return list.stream()
                .filter(app -> !app.rule().name().toString().equals(INTRODUCE_AXIOM_TACLET_NAME))
                .collect(ImmutableSLList.toImmutableList());
    }

    /**
     * removes RewriteTaclet from a list
     *
     * @param list from where the RewriteTaclet are removed
     * @return list without RewriteTaclets
     */
    public static ImmutableList<TacletApp> removeRewrites(ImmutableList<TacletApp> list) {
        ImmutableList<TacletApp> result = ImmutableSLList.nil();

        for (TacletApp tacletApp : list) {
            Taclet taclet = tacletApp.taclet();
            result = (taclet instanceof RewriteTaclet ? result : result.prepend(tacletApp));
        }
        return result;
    }

    private void initClutterRules() {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        clutterRuleSets = vs.getClutterRuleSets();
        clutterRules = vs.getClutterRules();
        vs.addPropertyChangeListener(e -> {
            clutterRuleSets = vs.getClutterRuleSets();
            clutterRules = vs.getClutterRules();
        });
    }

    /**
     * Creates the menu by adding all sub-menus and items.
     */
    private void createMenu(ImmutableList<TacletApp> find,
            ImmutableList<TacletApp> noFind,
            ImmutableList<BuiltInRule> builtInList) {
        ImmutableList<TacletApp> toAdd = sort(find, comp);
        boolean rulesAvailable = !find.isEmpty();

        if (getPos() != null && getPos().isSequent()) {
            rulesAvailable |= !noFind.isEmpty();
            toAdd = toAdd.prepend(noFind);
        }

        if (rulesAvailable) {
            addToMenu(toAdd);
        } else {
            add(new JLabel(NO_RULES_APPLICABLE));
        }

        createBuiltInRuleMenu(builtInList);
        createDelayedCutJoinMenu();
        createMergeRuleMenu();

        if (getPos() != null && getPos().isSequent()) {
            createSMTMenu();
        }
        createFocussedAutoModeMenu();
        addMacroMenu();

        addSeparator();
        addExtensionMenu();

        addSeparator();
        addClipboardItem();

        if (getPos() != null) {
            PosInOccurrence occ = getPos().getPosInOccurrence();
            if (occ != null && occ.posInTerm() != null) {
                JTerm t = (JTerm) occ.subTerm();
                createAbbrevSection(t);

                if (t.op() instanceof ProgramVariable var) {
                    if (var.getProgramElementName().getCreationInfo() != null) {
                        createNameCreationInfoSection();
                    }
                }
            }
        }
    }

    private void createBuiltInRuleMenu(ImmutableList<BuiltInRule> builtInList) {
        if (!builtInList.isEmpty()) {
            addSeparator();
            for (BuiltInRule builtInRule : builtInList) {
                addBuiltInRuleItem(builtInRule);
            }
        }
    }

    private void addMacroMenu() {
        ProofMacroMenu menu = new ProofMacroMenu(mediator, getPos().getPosInOccurrence());
        if (!menu.isEmpty()) {
            add(menu);
        }
    }

    private void createSMTMenu() {
        Collection<SolverTypeCollection> solverUnions = ProofIndependentSettings.DEFAULT_INSTANCE
                .getSMTSettings().getSolverUnions();
        if (!solverUnions.isEmpty()) {
            addSeparator();
        }

        for (SolverTypeCollection union : solverUnions) {
            if (union.isUsable()) {
                add(new JMenuItem(new SMTAction(union)));
            }
        }
    }

    private void createDelayedCutJoinMenu() {
        if (FeatureSettings.isFeatureActivated(ProofTreePopupFactory.FEATURE_DELAY_CUT)) {
            List<ProspectivePartner> partner = JoinIsApplicable.INSTANCE
                    .isApplicable(mediator.getSelectedGoal(), getPos().getPosInOccurrence());
            if (!partner.isEmpty()) {
                JMenuItem item = new JoinMenuItem(partner, mediator.getSelectedProof(), mediator);
                add(item);
            }
        }
    }

    /**
     * Creates the menu item for the "refocusing" merge rule which links partner nodes to merge
     * nodes.
     */
    private void createMergeRuleMenu() {
        if (MergeRule.isOfAdmissibleForm(mediator.getSelectedGoal(), getPos().getPosInOccurrence(),
            true)) {
            JMenuItem item = new MergeRuleMenuItem(mediator.getSelectedGoal(),
                getPos().getPosInOccurrence(), mediator);
            add(item);
        }
    }

    /**
     * adds an item for built-in rules (e.g., Run Simplify or Update Simplifier)
     */
    private void addBuiltInRuleItem(BuiltInRule builtInRule) {
        if (builtInRule == WhileInvariantRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            addBuiltInRuleItem(builtInRule, APPLY_RULE,
                "Applies a known and complete loop specification immediately.",
                ENTER_LOOP_SPECIFICATION,
                "Allows to modify an existing or to enter a new loop specification.");
        } else if (builtInRule instanceof BlockContractInternalRule) {
            // we add two items in this case: one for auto one for interactive
            addBuiltInRuleItem(builtInRule, APPLY_RULE,
                "Applies a known and complete block specification immediately.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.");
        } else if (builtInRule == BlockContractExternalRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            addBuiltInRuleItem(builtInRule, APPLY_RULE,
                "All available contracts of the block are combined and applied.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.");
        } else if (builtInRule == LoopContractInternalRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            addBuiltInRuleItem(builtInRule, APPLY_RULE,
                "Applies a known and complete loop block specification immediately.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.");
        } else if (builtInRule == LoopContractExternalRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            addBuiltInRuleItem(builtInRule, APPLY_RULE,
                "All available contracts of the loop block are combined and applied.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.");
        } else if (builtInRule == UseOperationContractRule.INSTANCE) {
            addBuiltInRuleItem(builtInRule, APPLY_CONTRACT,
                "All available contracts of the method are combined and applied.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.");
        }
        if (builtInRule != MergeRule.INSTANCE && builtInRule != LoopScopeInvariantRule.INSTANCE) {
            add(new ApplyBuiltInAction(builtInRule, builtInRule.toString(), ""));
        }
    }

    private void addBuiltInRuleItem(BuiltInRule builtInRule,
            String actionTextForForcedMode,
            String tooltipForcedMode,
            String actionTextForInteractiveMode,
            String tooltipInteractiveMode) {
        var menu = new JMenu(builtInRule.displayName());
        menu.add(
            new ApplyBuiltInForcelyAction(builtInRule, actionTextForForcedMode, tooltipForcedMode));
        menu.add(new ApplyBuiltInAction(builtInRule, actionTextForInteractiveMode,
            tooltipInteractiveMode));
        add(menu);
    }

    private void createFocussedAutoModeMenu() {
        addSeparator();
        add(actionFocussedAutoMode);
    }

    /**
     * This method is also used by the KeY ide has to be static and public.
     */
    public static ImmutableList<TacletApp> sort(ImmutableList<TacletApp> finds,
            TacletAppComparator comp) {
        ImmutableList<TacletApp> result = ImmutableSLList.nil();

        List<TacletApp> list = new ArrayList<>(finds.size());

        for (final TacletApp app : finds) {
            list.add(app);
        }

        list.sort(comp);

        for (final TacletApp app : list) {
            result = result.prepend(app);
        }

        return result;
    }

    private void createAbbrevSection(JTerm t) {
        AbbrevMap scm = mediator.getNotationInfo().getAbbrevMap();
        if (scm.containsTerm(t)) {
            add(new JMenuItem(actionChangeAbbreviation));
            if (scm.isEnabled(t)) {
                add(new JMenuItem(actionDisableAbbreviation));
            } else {
                add(new JMenuItem(actionEnableAbbreviation));
            }
        } else {
            add(new JMenuItem(actionCreateAbbreviation));
        }
    }

    /**
     * adds a TacletMenuItem for each taclet in the list and sets the given MenuControl as the
     * ActionListener
     *
     * @param taclets {@link ImmutableList<Taclet>} with the Taclets the items represent
     */
    private void addToMenu(ImmutableList<TacletApp> taclets) {
        var insHiddenItem = new ArrayList<TacletApp>();
        var insSystemInvItem = new ArrayList<TacletApp>();
        var normalTaclets = new ArrayList<TacletApp>();
        var rareTaclets = new ArrayList<TacletApp>();

        for (TacletApp app : taclets) {
            Taclet taclet = app.taclet();

            if (isHiddenTaclet(taclet)) {
                insHiddenItem.add(app);
                continue;
            }

            if (isSystemInvariantTaclet(taclet)) {
                insSystemInvItem.add(app);
                continue;
            }

            if (!mediator.getFilterForInteractiveProving().filter(taclet)) {
                continue;
            }

            if (isRareRule(taclet)) {
                rareTaclets.add(app);
            } else {
                normalTaclets.add(app);
            }
        }
        normalTaclets.addAll(rareTaclets);

        int currentSize = 0;
        JMenu target = this;
        for (TacletApp app : normalTaclets) {
            target.add(createMenuItem(app));
            ++currentSize;
            if (currentSize >= TOO_MANY_TACLETS_THRESHOLD) {
                JMenu newTarget = new JMenu(MORE_RULES);
                target.add(newTarget);
                target = newTarget;
                currentSize = 0;
            }
        }

        // add globally
        if (!insHiddenItem.isEmpty()) {
            add(createInsertHiddenMenu(insHiddenItem));
        }

        // add globally
        if (!insSystemInvItem.isEmpty()) {
            add(createSystemInvariantMenu(insSystemInvItem));
        }
    }

    /**
     * determines the sequent with the formulas to be added or null if the given taclet is not
     * thought to be displayed by this component
     *
     * @param taclet the Taclet
     * @return the sequent with the formulas to be added or null
     */
    private boolean isSystemInvariantTaclet(Taclet taclet) {
        if (!(taclet instanceof NoFindTaclet)
                || !taclet.displayName().startsWith("Insert implicit invariants of")) {
            return false;
        }
        return taclet.goalTemplates().size() == 1;
    }

    private JMenu createSystemInvariantMenu(List<TacletApp> insSystemInvItem) {
        var m = new JMenu("Insert Class Invariant");
        insSystemInvItem.sort(sortTacletByName);
        for (TacletApp app : insSystemInvItem) {
            // return displayName.replaceFirst("Insert invariants of ", "");
            m.add(new TacletAppAction(app));
        }
        return m;
    }

    /**
     * determines the sequent with the formulas to be added or null if the given taclet is not
     * thought to be displayed by this component
     *
     * @param taclet the Taclet
     * @return the sequent with the formulas to be added or null
     */
    private boolean isHiddenTaclet(Taclet taclet) {
        if (!(taclet instanceof NoFindTaclet)
                || !taclet.displayName().startsWith("insert_hidden")) {
            return false;
        }
        return taclet.goalTemplates().size() == 1;
    }

    private JMenu createInsertHiddenMenu(List<TacletApp> insHiddenItem) {
        var m = new JMenu("Insert Hidden");
        for (TacletApp tacletApp : insHiddenItem) {
            m.add(new TacletAppAction(tacletApp));
        }
        return m;
    }

    private boolean isRareRule(Taclet taclet) {
        if (clutterRules.contains(taclet.name().toString())) {
            return true;
        }
        return taclet.getRuleSets().stream()
                .anyMatch(it -> clutterRuleSets.contains(it.name().toString()));
    }

    private KeyAction createMenuItem(TacletApp app) {
        return new TacletAppAction(app);
    }

    private class FocussedRuleApplicationAction extends KeyAction {
        public FocussedRuleApplicationAction() {
            setName("Apply rules automatically here");
            setTooltip("<html>Initiates and restricts automatic rule applications on the "
                + "highlighted formula, term or sequent.<br> "
                + "'Shift + left mouse click' on the highlighted "
                + "entity does the same.</html>");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            new FocussedAutoModeUserAction(mediator, mediator.getSelectedProof(),
                getPos().getPosInOccurrence()).actionPerformed(e);
        }
    }

    public static class TacletAppComparator implements Comparator<TacletApp> {

        private int countFormulaSV(TacletSchemaVariableCollector c) {
            int formulaSV = 0;
            Iterator<SchemaVariable> it = c.varIterator();
            while (it.hasNext()) {
                SchemaVariable sv = it.next();
                if (sv instanceof FormulaSV) {
                    formulaSV++;
                }
            }

            return formulaSV;
        }

        /**
         * this is a rough estimation about the goal complexity. The complexity depends on the depth
         * of the term to be replaced. If no such term exists, we add a constant (maybe refined in
         * future)
         */
        private int measureGoalComplexity(ImmutableList<TacletGoalTemplate> l) {
            int result = 0;
            for (TacletGoalTemplate gt : l) {
                if (gt instanceof RewriteTacletGoalTemplate) {
                    if (((RewriteTacletGoalTemplate) gt).replaceWith() != null) {
                        result += ((RewriteTacletGoalTemplate) gt).replaceWith().depth();
                    }
                }
                if (!gt.sequent().isEmpty()) {
                    result += 10;
                }
            }
            return result;
        }

        /**
         * rough approximation of the program complexity
         */
        public int programComplexity(JavaBlock b) {
            if (b.isEmpty()) {
                return 0;
            }
            return new de.uka.ilkd.key.java.visitor.JavaASTWalker(b.program()) {
                private int counter = 0;

                @Override
                protected void doAction(ProgramElement pe) {
                    counter++;
                }

                public int getCounter() {
                    counter = 0;
                    start();
                    return counter;
                }
            }.getCounter();
        }

        @Override
        public int compare(TacletApp o1, TacletApp o2) {
            LinkedHashMap<String, Integer> map1 = score(o1);
            LinkedHashMap<String, Integer> map2 = score(o2);
            Iterator<Map.Entry<String, Integer>> it1 = map1.entrySet().iterator();
            Iterator<Map.Entry<String, Integer>> it2 = map2.entrySet().iterator();
            while (it1.hasNext() && it2.hasNext()) {
                String s1 = it1.next().getKey();
                String s2 = it2.next().getKey();
                if (!s1.equals(s2)) {
                    throw new IllegalStateException(
                        "A decision should have been made on a higher level ( " + s1 + "<->" + s2
                            + ")");
                }
                int v1 = map1.get(s1);
                int v2 = map2.get(s2);
                // the order will be reversed when the list is sorted
                if (v1 < v2) {
                    return 1;
                }
                if (v1 > v2) {
                    return -1;
                }
            }
            return 0;
        }

        /*
         * A score is a list of named values (comparable lexicographically). Smaller value means the
         * taclet should be higher on the list offered to the user. Two scores need not contain the
         * same named criteria, but the scoring scheme must force a decision before the first
         * divergence point.
         */
        public LinkedHashMap<String, Integer> score(TacletApp o1) {
            LinkedHashMap<String, Integer> map = new LinkedHashMap<>();

            final Taclet taclet1 = o1.taclet();

            map.put("closing", taclet1.goalTemplates().isEmpty() ? -1 : 1);

            boolean calc = false;
            for (RuleSet rs : taclet1.getRuleSets()) {
                String s = rs.name().toString();
                if (s.equals("simplify_literals") || s.equals("concrete") || s.equals("update_elim")
                        || s.equals("replace_known_left") || s.equals("replace_known_right")) {
                    calc = true;
                }
            }
            map.put("calc", calc ? -1 : 1);

            int formulaSV1 = 0;
            int cmpVar1 = 0;

            if (taclet1 instanceof FindTaclet) {
                map.put("has_find", -1);

                final JTerm find1 = ((FindTaclet) taclet1).find();
                int findComplexity1 = find1.depth();
                findComplexity1 += programComplexity(find1.javaBlock());
                map.put("find_complexity", -findComplexity1);

                // depth are equal. Number of schemavariables decides
                TacletSchemaVariableCollector coll1 = new TacletSchemaVariableCollector();
                find1.execPostOrder(coll1);
                formulaSV1 = countFormulaSV(coll1);
                cmpVar1 -= coll1.size();
                map.put("num_sv", -cmpVar1);

            } else {
                map.put("has_find", 1);
            }

            cmpVar1 = cmpVar1 - formulaSV1;
            map.put("sans_formula_sv", -cmpVar1);

            map.put("if_seq", taclet1.assumesSequent().isEmpty() ? 1 : -1);

            map.put("num_goals", taclet1.goalTemplates().size());

            map.put("goal_compl", measureGoalComplexity(taclet1.goalTemplates()));

            return map;
        }
    }

    private static boolean invalidAbbreviation(String s) {
        if (s == null || s.isBlank()) {
            return true;
        }
        return !s.chars()
                .allMatch(it -> Character.isAlphabetic(it) || Character.isDigit(it) || it == '_');
    }

    abstract class PIOAction extends KeyAction {
        @Override
        public final void actionPerformed(ActionEvent e) {
            PosInOccurrence occ = getPos().getPosInOccurrence();
            if (occ != null && occ.posInTerm() != null) {
                apply(occ);
            }
        }

        protected abstract void apply(@NonNull PosInOccurrence occ);
    }

    class CreateAbbreviationAction extends PIOAction {
        public CreateAbbreviationAction() {
            setName("Create abbreviation...");
        }

        @Override
        protected void apply(@NonNull PosInOccurrence occ) {
            // trim string, otherwise the main window gets too large (bug #1430)
            final String oldTerm = occ.subTerm().toString();
            final String term = oldTerm.length() > 200 ? oldTerm.substring(0, 200) : oldTerm;
            String abbreviation = (String) JOptionPane.showInputDialog(CurrentGoalViewMenu.this,
                "Enter abbreviation for term: \n" + term, "New Abbreviation",
                JOptionPane.QUESTION_MESSAGE, null, null, "");

            if (abbreviation == null)
                return;
            try {
                if (invalidAbbreviation(abbreviation)) {
                    JOptionPane.showMessageDialog(CurrentGoalViewMenu.this,
                        "Only letters, numbers and '_' are allowed for Abbreviations",
                        "Sorry", JOptionPane.INFORMATION_MESSAGE);
                } else {
                    final var map = mediator.getNotationInfo().getAbbrevMap();
                    if (map.containsAbbreviation(abbreviation)) {
                        var newAbbreviation = "old_" + abbreviation;
                        int answer = JOptionPane.showConfirmDialog(CurrentGoalViewMenu.this,
                            String.format(
                                "Abbreviation %s already bound. Do want to rename the previous binding to %s and proceed?",
                                abbreviation, newAbbreviation),
                            "Name collision resolution", JOptionPane.OK_CANCEL_OPTION,
                            JOptionPane.QUESTION_MESSAGE);

                        if (answer == JOptionPane.CANCEL_OPTION) {
                            return;
                        }

                        var prevTerm = map.getTerm(abbreviation);
                        var enabled = map.isEnabled(prevTerm);
                        map.remove(prevTerm);
                        map.put(prevTerm, newAbbreviation, enabled);
                    }
                    map.put((JTerm) occ.subTerm(), abbreviation, true);
                    getSequentView().printSequent();
                }
            } catch (AbbrevException sce) {
                JOptionPane.showMessageDialog(CurrentGoalViewMenu.this, sce.getMessage(), "Sorry",
                    JOptionPane.INFORMATION_MESSAGE);
            }
        }
    }

    class EnableAbbreviationAction extends PIOAction {
        public EnableAbbreviationAction() {
            setName("Enable abbreviation");
        }


        @Override
        protected void apply(@NonNull PosInOccurrence occ) {
            mediator.getNotationInfo().getAbbrevMap().setEnabled((JTerm) occ.subTerm(), true);
            getSequentView().printSequent();
        }
    }

    class DisableAbbreviationAction extends PIOAction {
        public DisableAbbreviationAction() {
            setName("Disable abbreviation");
        }

        @Override
        protected void apply(@NonNull PosInOccurrence occ) {
            mediator.getNotationInfo().getAbbrevMap().setEnabled((JTerm) occ.subTerm(), false);
            getSequentView().printSequent();
        }
    }

    class ChangeAbbreviationAction extends PIOAction {
        public ChangeAbbreviationAction() {
            setName("Change abbreviation...");
        }

        @Override
        protected void apply(@NonNull PosInOccurrence occ) {
            String abbreviation = (String) JOptionPane.showInputDialog(CurrentGoalViewMenu.this,
                "Enter abbreviation for term: \n" + occ.subTerm().toString(),
                "Change Abbreviation", JOptionPane.QUESTION_MESSAGE, null, null,
                mediator.getNotationInfo().getAbbrevMap().getAbbrev((JTerm) occ.subTerm())
                        .substring(1));
            try {
                if (abbreviation != null) {
                    if (invalidAbbreviation(abbreviation)) {
                        JOptionPane.showMessageDialog(CurrentGoalViewMenu.this,
                            "Only letters, numbers and '_'"
                                + "are allowed for Abbreviations",
                            "Sorry", JOptionPane.INFORMATION_MESSAGE);
                    } else {
                        mediator.getNotationInfo().getAbbrevMap()
                                .changeAbbrev((JTerm) occ.subTerm(), abbreviation);
                        getSequentView().printSequent();
                    }
                }
            } catch (AbbrevException sce) {
                JOptionPane.showMessageDialog(CurrentGoalViewMenu.this, sce.getMessage(), "Sorry",
                    JOptionPane.ERROR_MESSAGE);
            }
        }
    }

    private class SMTAction extends KeyAction {
        private final SolverTypeCollection solvers;

        public SMTAction(SolverTypeCollection solverTypes) {
            this.solvers = solverTypes;
            setName(solverTypes.toString());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            final Goal goal = mediator.getSelectedGoal();
            assert goal != null;
            Thread thread = new Thread(() -> {
                DefaultSMTSettings settings =
                    new DefaultSMTSettings(goal.proof().getSettings().getSMTSettings(),
                        ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                        goal.proof().getSettings().getNewSMTSettings(), goal.proof());
                SolverLauncher launcher = new SolverLauncher(settings);
                launcher.addListener(new SolverListener(settings, goal.proof()));
                Collection<SMTProblem> list = new LinkedList<>();
                list.add(new SMTProblem(goal));
                launcher.launch(solvers.getTypes(), list, goal.proof().getServices());
            }, "SMTRunner");
            thread.start();
        }
    }

    private class TacletAppAction extends KeyAction {
        private final TacletApp app;

        public TacletAppAction(TacletApp tacletApp) {
            this.app = tacletApp;
            setName(tacletApp.displayName());

            SVInstantiations instantiations;
            if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .getShowUninstantiatedTaclet()) {
                instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;
            } else {
                instantiations = tacletApp.instantiations();
            }

            var tp = SequentViewLogicPrinter.purePrinter(68,
                mediator.getNotationInfo(),
                mediator.getServices(),
                MainWindow.getInstance().getVisibleTermLabels());

            tp.printTaclet(tacletApp.taclet(), instantiations,
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getShowWholeTaclet(),
                false);

            int maxTooltipLines =
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getMaxTooltipLines();

            // replaced the old code here to fix #1340. (MU)
            String w = tp.result();
            int nlCount = 0;
            int sbl = w.length();
            boolean truncated = false;
            for (int i = 0; i < sbl && !truncated; i++) {
                if (w.charAt(i) == '\n') {
                    nlCount += 1;
                    if (nlCount > maxTooltipLines) {
                        w = w.substring(0, i);
                        truncated = true;
                    }
                }
            }

            StringBuilder tacletString = new StringBuilder();
            tacletString.append("<html><pre>");
            tacletString.append(StringUtil.ascii2html(w));
            tacletString.append("</pre>");
            if (truncated) {
                tacletString.append("\n<b>!!</b><i> Message has been truncated. "
                    + "See View &rarr; ToolTip Options.</i>");
            }

            this.setTooltip(tacletString.toString());

            // This is a GUI improvement proposed by Stijn: Show the formula
            // you add instead of "Insert hidden"
            if (isHiddenTaclet(tacletApp.taclet())) {
                ImmutableList<TacletGoalTemplate> templates = tacletApp.taclet().goalTemplates();
                if (templates.size() == 1) {
                    var printer = LogicPrinter.purePrinter(
                        mediator.getNotationInfo(), mediator.getServices());
                    printer.setInstantiation(tacletApp.instantiations());
                    printer.printSequent(templates.head().sequent());
                    String s = printer.result();
                    if (s.length() > 40) {
                        s = s.substring(0, 37) + "...";
                    }
                    this.setName(s);
                }
            }
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            getSequentView().selectedTaclet(app, getPos());
        }
    }

    private class ApplyBuiltInAction extends KeyAction {
        protected final BuiltInRule rule;

        public ApplyBuiltInAction(BuiltInRule rule, String text, String tooltip) {
            this.rule = rule;
            setName(text);
            setTooltip(tooltip);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            mediator.getUI().getProofControl().selectedBuiltInRule(mediator.getSelectedGoal(),
                rule, getPos().getPosInOccurrence(), false, true);
        }
    }

    private class ApplyBuiltInForcelyAction extends ApplyBuiltInAction {
        public ApplyBuiltInForcelyAction(BuiltInRule rule, String text, String tooltip) {
            super(rule, text, tooltip);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            mediator.getUI().getProofControl().selectedBuiltInRule(mediator.getSelectedGoal(),
                rule, getPos().getPosInOccurrence(), true, true);
        }
    }
}
