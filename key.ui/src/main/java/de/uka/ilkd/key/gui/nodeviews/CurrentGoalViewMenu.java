/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofMacroMenu;
import de.uka.ilkd.key.gui.actions.useractions.FocussedAutoModeUserAction;
import de.uka.ilkd.key.gui.join.JoinMenuItem;
import de.uka.ilkd.key.gui.mergerule.MergeRuleMenuItem;
import de.uka.ilkd.key.gui.smt.SMTMenuItem;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.join.JoinIsApplicable;
import de.uka.ilkd.key.proof.join.ProspectivePartner;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverTypeCollection;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * The menu shown by a {@link CurrentGoalViewListener} when the user clicks on a
 * {@link CurrentGoalView}, i.e. when the user clicks on the sequent.
 *
 * Shows all {@link Taclet}s that are applicable at a selected position.
 */
public final class CurrentGoalViewMenu extends SequentViewMenu<CurrentGoalView> {
    private static final long serialVersionUID = 8151230546928796116L;

    private static final String INTRODUCE_AXIOM_TACLET_NAME = "introduceAxiom";
    private static final String CREATE_ABBREVIATION = "Create abbreviation...";
    private static final String ENABLE_ABBREVIATION = "Enable abbreviation";
    private static final String DISABLE_ABBREVIATION = "Disable abbreviation";
    private static final String CHANGE_ABBREVIATION = "Change abbreviation...";
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
            removeIntroduceAxiomTaclet(noFindList), builtInList, new MenuControl());
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
     * removes RewriteTaclet from list
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
     *
     * @param control the action listener.
     */
    private void createMenu(ImmutableList<TacletApp> find, ImmutableList<TacletApp> noFind,
            ImmutableList<BuiltInRule> builtInList, MenuControl control) {
        addActionListener(control);

        ImmutableList<TacletApp> toAdd = sort(find, comp);
        boolean rulesAvailable = find.size() > 0;

        if (getPos() != null && getPos().isSequent()) {
            rulesAvailable |= noFind.size() > 0;
            toAdd = toAdd.prepend(noFind);
        }

        if (rulesAvailable) {
            addToMenu(toAdd, control);
        } else {
            add(new JLabel(NO_RULES_APPLICABLE));
        }

        createBuiltInRuleMenu(builtInList, control);
        createDelayedCutJoinMenu(control);
        createMergeRuleMenu();

        if (getPos() != null && getPos().isSequent()) {
            createSMTMenu(control);
        }
        createFocussedAutoModeMenu(control);
        addMacroMenu();

        addSeparator();
        addExtensionMenu();

        addSeparator();
        addClipboardItem(control);

        if (getPos() != null) {
            PosInOccurrence occ = getPos().getPosInOccurrence();
            if (occ != null && occ.posInTerm() != null) {
                Term t = occ.subTerm();
                createAbbrevSection(t, control);

                if (t.op() instanceof ProgramVariable) {
                    ProgramVariable var = (ProgramVariable) t.op();
                    if (var.getProgramElementName().getCreationInfo() != null) {
                        createNameCreationInfoSection(control);
                    }
                }
            }
        }
    }

    private void createBuiltInRuleMenu(ImmutableList<BuiltInRule> builtInList,
            MenuControl control) {

        if (!builtInList.isEmpty()) {
            addSeparator();
            for (BuiltInRule builtInRule : builtInList) {
                addBuiltInRuleItem(builtInRule, control);
            }
        }
    }

    private void addMacroMenu() {
        ProofMacroMenu menu = new ProofMacroMenu(mediator, getPos().getPosInOccurrence());
        if (!menu.isEmpty()) {
            add(menu);
        }
    }

    private void createSMTMenu(MenuControl control) {
        Collection<SolverTypeCollection> solverUnions = ProofIndependentSettings.DEFAULT_INSTANCE
                .getSMTSettings().getSolverUnions(Main.isExperimentalMode());
        if (!solverUnions.isEmpty()) {
            addSeparator();
        }
        for (SolverTypeCollection union : solverUnions) {
            if (union.isUsable()) {
                JMenuItem item = new SMTMenuItem(union);
                item.addActionListener(control);
                add(item);
            }
        }

    }

    private void createDelayedCutJoinMenu(MenuControl control) {
        if (Main.isExperimentalMode()) {
            List<ProspectivePartner> partner = JoinIsApplicable.INSTANCE
                    .isApplicable(mediator.getSelectedGoal(), getPos().getPosInOccurrence());
            if (!partner.isEmpty()) {
                JMenuItem item = new JoinMenuItem(partner, mediator.getSelectedProof(), mediator);
                add(item);
            }
        }
    }

    /**
     * Creates the menu item for the "defocusing" merge rule which links partner nodes to merge
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
     * adds an item for built in rules (e.g. Run Simplify or Update Simplifier)
     */
    private void addBuiltInRuleItem(BuiltInRule builtInRule, MenuControl control) {
        JMenuItem item = null;
        if (builtInRule == LoopScopeInvariantRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
        } else if (builtInRule == WhileInvariantRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            item = new MenuItemForTwoModeRules(builtInRule.displayName(), APPLY_RULE,
                "Applies a known and complete loop specification immediately.",
                ENTER_LOOP_SPECIFICATION,
                "Allows to modify an existing or to enter a new loop specification.", builtInRule);
        } else if (builtInRule == BlockContractInternalRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            item = new MenuItemForTwoModeRules(builtInRule.displayName(), APPLY_RULE,
                "Applies a known and complete block specification immediately.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.",
                builtInRule);
        } else if (builtInRule == BlockContractExternalRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            item = new MenuItemForTwoModeRules(builtInRule.displayName(), APPLY_RULE,
                "All available contracts of the block are combined and applied.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.",
                builtInRule);
        } else if (builtInRule == LoopContractInternalRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            item = new MenuItemForTwoModeRules(builtInRule.displayName(), APPLY_RULE,
                "Applies a known and complete loop block specification immediately.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.",
                builtInRule);
        } else if (builtInRule == LoopContractExternalRule.INSTANCE) {
            // we add two items in this case: one for auto one for interactive
            item = new MenuItemForTwoModeRules(builtInRule.displayName(), APPLY_RULE,
                "All available contracts of the loop block are combined and applied.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.",
                builtInRule);
        } else if (builtInRule == UseOperationContractRule.INSTANCE) {
            item = new MenuItemForTwoModeRules(builtInRule.displayName(), APPLY_CONTRACT,
                "All available contracts of the method are combined and applied.",
                CHOOSE_AND_APPLY_CONTRACT, "Asks to select the contract to be applied.",
                builtInRule);
        } else if (builtInRule == MergeRule.INSTANCE) {
            // (DS) MergeRule has a special menu item, and thus is not added here.
        } else {
            item = new DefaultBuiltInRuleMenuItem(builtInRule);
        }

        if (item != null) {
            item.addActionListener(control);
            add(item);
        }
    }

    private void createFocussedAutoModeMenu(MenuControl control) {
        addSeparator();
        JMenuItem item = new FocussedRuleApplicationMenuItem();
        item.addActionListener(control);
        add(item);
    }

    /**
     * This method is also used by the KeYIDE has to be static and public.
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

    private void createAbbrevSection(Term t, MenuControl control) {
        AbbrevMap scm = mediator.getNotationInfo().getAbbrevMap();
        JMenuItem sc = null;
        if (scm.containsTerm(t)) {
            sc = new JMenuItem(CHANGE_ABBREVIATION);
            sc.addActionListener(control);
            add(sc);
            if (scm.isEnabled(t)) {
                sc = new JMenuItem(DISABLE_ABBREVIATION);
            } else {
                sc = new JMenuItem(ENABLE_ABBREVIATION);
            }
        } else {
            sc = new JMenuItem(CREATE_ABBREVIATION);
        }
        sc.addActionListener(control);
        add(sc);
    }

    /**
     * adds a TacletMenuItem for each taclet in the list and sets the given MenuControl as the
     * ActionListener
     *
     * @param taclets {@link ImmutableList<Taclet>} with the Taclets the items represent
     * @param control the ActionListener
     */
    private void addToMenu(ImmutableList<TacletApp> taclets, MenuControl control) {

        final InsertHiddenTacletMenuItem insHiddenItem = new InsertHiddenTacletMenuItem(
            MainWindow.getInstance(), mediator.getNotationInfo(), mediator.getServices());

        final InsertionTacletBrowserMenuItem insSystemInvItem =
            new InsertSystemInvariantTacletMenuItem(MainWindow.getInstance(),
                mediator.getNotationInfo(), mediator.getServices());

        List<TacletApp> normalTaclets = new ArrayList<>();
        List<TacletApp> rareTaclets = new ArrayList<>();

        for (TacletApp app : taclets) {
            Taclet taclet = app.taclet();

            if (insHiddenItem.isResponsible(taclet)) {
                insHiddenItem.add(app);
                continue;
            }

            if (insSystemInvItem.isResponsible(taclet)) {
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
            target.add(createMenuItem(app, control));
            ++currentSize;
            if (currentSize >= TOO_MANY_TACLETS_THRESHOLD) {
                JMenu newTarget = new JMenu(MORE_RULES);
                target.add(newTarget);
                target = newTarget;
                currentSize = 0;
            }
        }

        // add globally
        if (insHiddenItem.getAppSize() > 0) {
            add(insHiddenItem);
            insHiddenItem.addActionListener(control);
        }

        // add globally
        if (insSystemInvItem.getAppSize() > 0) {
            add(insSystemInvItem);
            insSystemInvItem.addActionListener(control);
        }

        // JMenu more = new JMenu(MORE_RULES);

        /*
         * for (final TacletApp app : taclets) { final Taclet taclet = app.taclet(); if
         * (!mediator.getFilterForInteractiveProving().filter(taclet)) { continue; }
         *
         * if (!insHiddenItem.isResponsible(taclet) && !insSystemInvItem.isResponsible(taclet)) {
         * final DefaultTacletMenuItem item = new DefaultTacletMenuItem(this, app,
         * mediator.getNotationInfo(), mediator.getServices()); item.addActionListener(control);
         * boolean rareRule = false; for (RuleSet rs : taclet.getRuleSets()) { if
         * (clutterRuleSets.contains(rs.name())) { rareRule = true; } } if
         * (clutterRules.contains(taclet.name())) { rareRule = true; }
         *
         * if (rareRule) { more.add(item); } else { add(item); } } }
         */

        /*
         * if (more.getItemCount() > 0) { add(more); }
         */
    }

    private boolean isRareRule(Taclet taclet) {
        if (clutterRules.contains(taclet.name().toString())) {
            return true;
        }
        return taclet.getRuleSets().stream()
                .anyMatch(it -> clutterRuleSets.contains(it.name().toString()));
    }

    private Component createMenuItem(TacletApp app, MenuControl control) {
        final DefaultTacletMenuItem item =
            new DefaultTacletMenuItem(app, mediator.getNotationInfo(), mediator.getServices());
        item.addActionListener(control);
        return item;
    }

    /**
     * makes submenus invisible
     */
    void invisible() {
        for (int i = 0; i < getMenuComponentCount(); i++) {
            if (getMenuComponent(i) instanceof JMenu) {
                ((JMenu) getMenuComponent(i)).getPopupMenu().setVisible(false);
            }
        }
    }

    /**
     * ActionListener
     */
    class MenuControl extends SequentViewMenu<CurrentGoalView>.MenuControl {

        private boolean validAbbreviation(String s) {
            if (s == null || s.length() == 0) {
                return false;
            }
            for (int i = 0; i < s.length(); i++) {
                if (!((s.charAt(i) <= '9' && s.charAt(i) >= '0')
                        || (s.charAt(i) <= 'z' && s.charAt(i) >= 'a')
                        || (s.charAt(i) <= 'Z' && s.charAt(i) >= 'A') || s.charAt(i) == '_')) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (e.getSource() instanceof TacletMenuItem) {
                ((CurrentGoalView) (getPopupMenu().getInvoker()))
                        .selectedTaclet(((TacletMenuItem) e.getSource()).connectedTo(), getPos());
            } else if (e.getSource() instanceof SMTMenuItem) {
                final SMTMenuItem item = (SMTMenuItem) e.getSource();
                final SolverTypeCollection solverUnion = item.getSolverUnion();
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
                    launcher.launch(solverUnion.getTypes(), list, goal.proof().getServices());
                }, "SMTRunner");
                thread.start();
            } else if (e.getSource() instanceof BuiltInRuleMenuItem) {

                final BuiltInRuleMenuItem birmi = (BuiltInRuleMenuItem) e.getSource();
                // This method delegates the request only to the UserInterfaceControl which
                // implements the functionality.
                // No functionality is allowed in this method body!
                mediator.getUI().getProofControl().selectedBuiltInRule(mediator.getSelectedGoal(),
                    birmi.connectedTo(), getPos().getPosInOccurrence(), birmi.forcedApplication(),
                    true);

            } else if (e.getSource() instanceof FocussedRuleApplicationMenuItem) {
                new FocussedAutoModeUserAction(mediator, mediator.getSelectedProof(),
                    getPos().getPosInOccurrence()).actionPerformed(e);
            } else {
                PosInOccurrence occ = getPos().getPosInOccurrence();

                switch (((JMenuItem) e.getSource()).getText()) {
                case DISABLE_ABBREVIATION:
                    if (occ != null && occ.posInTerm() != null) {
                        mediator.getNotationInfo().getAbbrevMap().setEnabled(occ.subTerm(), false);
                        getSequentView().printSequent();
                    }

                    break;

                case ENABLE_ABBREVIATION:
                    if (occ != null && occ.posInTerm() != null) {
                        mediator.getNotationInfo().getAbbrevMap().setEnabled(occ.subTerm(), true);
                        getSequentView().printSequent();
                    }

                    break;

                case CREATE_ABBREVIATION:
                    if (occ != null && occ.posInTerm() != null) {
                        // trim string, otherwise window gets too large (bug #1430)
                        final String oldTerm = occ.subTerm().toString();
                        final String term =
                            oldTerm.length() > 200 ? oldTerm.substring(0, 200) : oldTerm;
                        String abbreviation = (String) JOptionPane.showInputDialog(new JFrame(),
                            "Enter abbreviation for term: \n" + term, "New Abbreviation",
                            JOptionPane.QUESTION_MESSAGE, null, null, "");

                        try {
                            if (abbreviation != null) {
                                if (!validAbbreviation(abbreviation)) {
                                    JOptionPane.showMessageDialog(new JFrame(),
                                        "Only letters, numbers and '_' are allowed for Abbreviations",
                                        "Sorry", JOptionPane.INFORMATION_MESSAGE);
                                } else {
                                    mediator.getNotationInfo().getAbbrevMap().put(occ.subTerm(),
                                        abbreviation, true);
                                    getSequentView().printSequent();
                                }
                            }
                        } catch (AbbrevException sce) {
                            JOptionPane.showMessageDialog(new JFrame(), sce.getMessage(), "Sorry",
                                JOptionPane.INFORMATION_MESSAGE);
                        }
                    }

                    break;

                case CHANGE_ABBREVIATION:
                    if (occ != null && occ.posInTerm() != null) {
                        String abbreviation = (String) JOptionPane.showInputDialog(new JFrame(),
                            "Enter abbreviation for term: \n" + occ.subTerm().toString(),
                            "Change Abbreviation", JOptionPane.QUESTION_MESSAGE, null, null,
                            mediator.getNotationInfo().getAbbrevMap().getAbbrev(occ.subTerm())
                                    .substring(1));
                        try {
                            if (abbreviation != null) {
                                if (!validAbbreviation(abbreviation)) {
                                    JOptionPane.showMessageDialog(new JFrame(),
                                        "Only letters, numbers and '_'"
                                            + "are allowed for Abbreviations",
                                        "Sorry", JOptionPane.INFORMATION_MESSAGE);
                                } else {
                                    mediator.getNotationInfo().getAbbrevMap()
                                            .changeAbbrev(occ.subTerm(), abbreviation);
                                    getSequentView().printSequent();
                                }
                            }
                        } catch (AbbrevException sce) {
                            JOptionPane.showMessageDialog(new JFrame(), sce.getMessage(), "Sorry",
                                JOptionPane.INFORMATION_MESSAGE);
                        }
                    }

                    break;

                default:
                    super.actionPerformed(e);
                }
            }
        }
    }

    static class FocussedRuleApplicationMenuItem extends JMenuItem {
        private static final String APPLY_RULES_AUTOMATICALLY_HERE =
            "Apply rules automatically here";
        /**
         *
         */
        private static final long serialVersionUID = -6486650015103963268L;

        public FocussedRuleApplicationMenuItem() {
            super(APPLY_RULES_AUTOMATICALLY_HERE);
            setToolTipText("<html>Initiates and restricts automatic rule applications on the "
                + "highlighted formula, term or sequent.<br> "
                + "'Shift + left mouse click' on the highlighted "
                + "entity does the same.</html>");
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
         * of the term to be replaced. If no such term exists we add a constant (may be refined in
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

            map.put("closing", taclet1.goalTemplates().size() == 0 ? -1 : 1);

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

                final Term find1 = ((FindTaclet) taclet1).find();
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

            map.put("if_seq", taclet1.ifSequent().isEmpty() ? 1 : -1);

            map.put("num_goals", taclet1.goalTemplates().size());

            map.put("goal_compl", measureGoalComplexity(taclet1.goalTemplates()));

            return map;
        }
    }
}
