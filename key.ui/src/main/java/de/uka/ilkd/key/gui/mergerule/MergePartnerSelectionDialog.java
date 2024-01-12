/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.mergerule;

import java.awt.*;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.text.html.HTMLDocument;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.utilities.WrapLayout;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * JDialog for selecting a subset of candidate goals as partners for a {@link MergeRule}
 * application.
 *
 * @author Dominic Scheurer
 */
public class MergePartnerSelectionDialog extends JDialog {

    private static final long serialVersionUID = -1460097562546341922L;

    /** The tooltip hint for the checkbox. */
    private static final String CB_SELECT_CANDIDATE_HINT =
        "Select to add shown state as a merge partner.";

    /** The tooltip for the OK button */
    private static final String CHOOSE_ALL_BTN_TOOLTIP_TXT =
        "Select all proposed goals as merge partners. "
            + "Only enabled if the merge is applicable for all goals and the chosen merge procedure.";
    /** The tooltip for the choose-all button */
    private static final String OK_BTN_TOOLTIP_TXT = "Select the chosen goals as merge partners. "
        + "Only enabled if at least one goal is chosen and the merge is applicable for the "
        + "chosen goals and merge procedure.";

    /** The initial size of this dialog. */
    private static final Dimension INITIAL_SIZE = new Dimension(900, 450);

    /**
     * The font for the JEditorPanes. Should resemble the standard font of KeY for proofs etc.
     */
    private static final Font TXT_AREA_FONT = new Font(Font.MONOSPACED, Font.PLAIN, 14);

    private final static MainWindow MAIN_WINDOW_INSTANCE = MainWindow.getInstance();

    /** Comparator for goals; sorts by serial nr. of the node */
    private static final Comparator<MergePartner> GOAL_COMPARATOR =
        Comparator.comparingInt(o -> o.getGoal().node().serialNr());

    private LinkedList<MergePartner> candidates = null;
    private Services services = null;
    private Pair<Goal, PosInOccurrence> mergeGoalPio = null;

    /** The chosen goals. */
    private SortedSet<MergePartner> chosenGoals = new TreeSet<>(GOAL_COMPARATOR);

    /** The chosen merge method. */
    private MergeProcedure chosenRule = MergeProcedure.getMergeProcedures().head();

    /** The chosen distinguishing formula */
    private Term chosenDistForm = null;

    private JEditorPane txtPartner1 = null;
    private JEditorPane txtPartner2 = null;
    private JComboBox<String> cmbCandidates = null;
    private JCheckBox cbSelectCandidate = null;
    private ButtonGroup bgMergeMethods = null;
    private final JTextField txtDistForm;

    private JScrollPane scrpPartner1 = null;
    private JScrollPane scrpPartner2 = null;

    private JButton okButton = null;
    private JButton chooseAllButton = null;

    private MergePartnerSelectionDialog() {
        super(MAIN_WINDOW_INSTANCE, "Select partner node for merge operation", true);

        // Text areas for goals to merge
        txtPartner1 = new JEditorPane();
        txtPartner2 = new JEditorPane();
        for (JEditorPane jep : new JEditorPane[] { txtPartner1, txtPartner2 }) {
            jep.setEditable(false);
            jep.setContentType("text/html");

            // Set font
            String cssRule = "body { font-family: " + TXT_AREA_FONT.getFamily() + "; "
                + "font-size: " + TXT_AREA_FONT.getSize() + "pt; }";
            ((HTMLDocument) jep.getDocument()).getStyleSheet().addRule(cssRule);
        }

        scrpPartner1 = new JScrollPane(txtPartner1);
        scrpPartner2 = new JScrollPane(txtPartner2);

        // Goal selection dropdown field and checkbox
        cmbCandidates = new JComboBox<>();
        cmbCandidates.setMaximumSize(new Dimension(Integer.MAX_VALUE, 20));
        cmbCandidates.addItemListener(e -> {
            MergePartner selectedCandidate = getSelectedCandidate();

            setHighlightedSequentForArea(selectedCandidate.getGoal(),
                selectedCandidate.getPio(), txtPartner2);

            cbSelectCandidate.setSelected(chosenGoals.contains(selectedCandidate));
        });

        addComponentListener(new ComponentAdapter() {
            @Override
            public void componentResized(ComponentEvent e) {
                super.componentResized(e);

                int halfWidth = getWidth() / 2;
                scrpPartner1.setPreferredSize(new Dimension(halfWidth, scrpPartner1.getHeight()));
                scrpPartner2.setPreferredSize(new Dimension(halfWidth, scrpPartner2.getHeight()));
            }
        });

        cbSelectCandidate = new JCheckBox();
        cbSelectCandidate.setToolTipText(CB_SELECT_CANDIDATE_HINT);
        cbSelectCandidate.addActionListener(e -> {
            if (cbSelectCandidate.isSelected()) {
                chosenGoals.add(getSelectedCandidate());
            } else {
                chosenGoals.remove(getSelectedCandidate());
            }

            checkApplicable();
        });

        bgMergeMethods = new ButtonGroup();
        for (final MergeProcedure rule : MergeProcedure.getMergeProcedures()) {
            JRadioButton rb = new JRadioButton(rule.toString());
            rb.setSelected(true);

            rb.addActionListener(e -> {
                chosenRule = rule;

                checkApplicable();
            });
            bgMergeMethods.add(rb);
        }

        // Merge state container
        JPanel mergeStateContainer = new JPanel();
        mergeStateContainer.setLayout(new BoxLayout(mergeStateContainer, BoxLayout.Y_AXIS));
        mergeStateContainer.add(scrpPartner1);

        TitledBorder mergeStateContainerTitle = BorderFactory.createTitledBorder("State to merge");
        mergeStateContainerTitle.setTitleJustification(TitledBorder.LEFT);
        mergeStateContainer.setBorder(mergeStateContainerTitle);

        // Merge partner container
        JPanel partnerContainer = new JPanel();
        partnerContainer.setLayout(new BoxLayout(partnerContainer, BoxLayout.Y_AXIS));
        partnerContainer.add(scrpPartner2);

        JPanel selectionContainer = new JPanel();
        selectionContainer.setLayout(new BoxLayout(selectionContainer, BoxLayout.X_AXIS));
        selectionContainer.add(cbSelectCandidate);
        selectionContainer.add(cmbCandidates);

        partnerContainer.add(selectionContainer);

        TitledBorder txtPartner2Title =
            BorderFactory.createTitledBorder("Potential merge partners");
        txtPartner2Title.setTitleJustification(TitledBorder.LEFT);
        partnerContainer.setBorder(txtPartner2Title);

        // Upper container
        JPanel upperContainer = new JPanel();
        upperContainer.setLayout(new BoxLayout(upperContainer, BoxLayout.X_AXIS));
        upperContainer.add(mergeStateContainer);
        upperContainer.add(partnerContainer);

        // Merge rules container
        JPanel mergeRulesContainer = new JPanel();
        mergeRulesContainer.setLayout(new WrapLayout());

        for (Enumeration<AbstractButton> e = bgMergeMethods.getElements(); e.hasMoreElements();) {
            JRadioButton rb = (JRadioButton) e.nextElement();
            mergeRulesContainer.add(rb);
        }

        TitledBorder mergeRulesContainerTitle =
            BorderFactory.createTitledBorder("Concrete merge procedure to apply");
        mergeRulesContainerTitle.setTitleJustification(TitledBorder.LEFT);
        mergeRulesContainerTitle.setBorder(mergeStateContainerTitle);
        mergeRulesContainer.setBorder(mergeRulesContainerTitle);

        // Distinguishing method input field container
        txtDistForm = new JTextField();
        txtDistForm.setMargin(new Insets(5, 0, 5, 0));
        txtDistForm.addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                chosenDistForm = MergeRuleUtils.translateToFormula(services, txtDistForm.getText());

                if (chosenDistForm == null || !isSuitableDistFormula()) {
                    txtDistForm.setForeground(Color.RED);
                } else {
                    txtDistForm.setForeground(Color.BLACK);
                }

                checkApplicable();
            }
        });

        JPanel distFormContainer = new JPanel();
        distFormContainer.setLayout(new BorderLayout());

        distFormContainer.add(txtDistForm, BorderLayout.CENTER);

        TitledBorder distFormContainerTitle = BorderFactory.createTitledBorder(
            "Distinguishing formula (leave empty for automatic generation!)");
        distFormContainerTitle.setTitleJustification(TitledBorder.LEFT);
        distFormContainer.setBorder(distFormContainerTitle);

        // Control buttons container: OK / Cancel
        okButton = new JButton("OK");
        chooseAllButton = new JButton("Choose All");
        JButton cancelButton = new JButton("Cancel");

        okButton.setAlignmentX(CENTER_ALIGNMENT);
        chooseAllButton.setAlignmentX(CENTER_ALIGNMENT);
        cancelButton.setAlignmentX(CENTER_ALIGNMENT);

        okButton.setToolTipText(OK_BTN_TOOLTIP_TXT);
        chooseAllButton.setToolTipText(CHOOSE_ALL_BTN_TOOLTIP_TXT);

        okButton.addActionListener(e -> {
            setVisible(false);
            dispose();
        });

        chooseAllButton.addActionListener(e -> {
            chosenGoals.addAll(candidates);
            setVisible(false);
        });

        cancelButton.addActionListener(e -> {
            chosenGoals = null;
            setVisible(false);
        });

        JPanel ctrlBtnsContainer = new JPanel();
        ctrlBtnsContainer.setLayout(new BoxLayout(ctrlBtnsContainer, BoxLayout.X_AXIS));
        ctrlBtnsContainer.add(Box.createHorizontalGlue());
        ctrlBtnsContainer.add(okButton);
        Dimension fillerDim = new Dimension(30, 40);
        ctrlBtnsContainer.add(new Box.Filler(fillerDim, fillerDim, fillerDim));
        ctrlBtnsContainer.add(chooseAllButton);
        ctrlBtnsContainer.add(new Box.Filler(fillerDim, fillerDim, fillerDim));
        ctrlBtnsContainer.add(cancelButton);
        ctrlBtnsContainer.add(Box.createHorizontalGlue());

        JPanel lowerContainer = new JPanel();
        Dimension verticalFillerDim = new Dimension(0, 10);
        lowerContainer.setLayout(new BoxLayout(lowerContainer, BoxLayout.Y_AXIS));
        lowerContainer.add(mergeRulesContainer);
        lowerContainer.add(new Box.Filler(verticalFillerDim, verticalFillerDim, verticalFillerDim));
        lowerContainer.add(distFormContainer);
        lowerContainer.add(new Box.Filler(verticalFillerDim, verticalFillerDim, verticalFillerDim));
        lowerContainer.add(ctrlBtnsContainer);

        // Add components to content pane
        getContentPane().add(upperContainer, BorderLayout.CENTER);
        getContentPane().add(lowerContainer, BorderLayout.SOUTH);

        setSize(INITIAL_SIZE);
        setLocationRelativeTo(MAIN_WINDOW_INSTANCE);
    }

    /**
     * Creates a new merge partner selection dialog.
     *
     * @param mergeGoal The first (already chosen) merge partner.
     * @param pio Position of Update-Modality-Postcondition formula in the mergeNode.
     * @param candidates Potential merge candidates.
     * @param services The services object.
     */
    public MergePartnerSelectionDialog(Goal mergeGoal, PosInOccurrence pio,
            ImmutableList<MergePartner> candidates, Services services) {

        this();
        this.services = services;

        this.candidates = new LinkedList<>();
        this.mergeGoalPio = new Pair<>(mergeGoal, pio);

        for (MergePartner candidate : candidates) {
            int insPos = Collections.binarySearch(this.candidates, candidate, GOAL_COMPARATOR);

            insPos = (insPos + 1) * -1;
            this.candidates.add(insPos, candidate);
        }

        setHighlightedSequentForArea(mergeGoal, pio, txtPartner1);
        loadCandidates();

    }

    /**
     * @return All chosen merge partners.
     */
    public ImmutableList<MergePartner> getChosenCandidates() {
        ImmutableSLList<MergePartner> result = ImmutableSLList.nil();

        if (chosenGoals != null) {
            return result.append(chosenGoals);
        } else {
            return result;
        }
    }

    /**
     * @param <T>
     * @return The chosen merge rule.
     */
    @SuppressWarnings("unchecked")
    public <T extends MergeProcedure> T getChosenMergeRule() {
        MergeProcedureCompletion<T> completion =
            (MergeProcedureCompletion<T>) MergeProcedureCompletion
                    .getCompletionForClass(chosenRule.getClass());

        return completion.complete((T) chosenRule, mergeGoalPio, chosenGoals);
    }

    /**
     * @return The chosen distinguishing formula. If null, an automatic generation of the
     *         distinguishing formula should be performed.
     */
    public Term getChosenDistinguishingFormula() {
        return isSuitableDistFormula() ? chosenDistForm : null;
    }

    /**
     * Checks whether the merge rule is applicable for the given set of candidates.
     *
     * @param theCandidates Candidates to instantiate the merge rule application with.
     * @return true iff the merge rule instance induced by the given set of candidates is
     *         applicable.
     */
    private boolean isApplicableForCandidates(ImmutableList<MergePartner> theCandidates) {
        if (mergeGoalPio != null && candidates != null && chosenRule != null) {
            MergeRuleBuiltInRuleApp mergeRuleApp = (MergeRuleBuiltInRuleApp) MergeRule.INSTANCE
                    .createApp(mergeGoalPio.second, services);

            mergeRuleApp.setMergeNode(mergeGoalPio.first.node());
            mergeRuleApp.setConcreteRule(chosenRule);
            mergeRuleApp.setMergePartners(theCandidates);

            return mergeRuleApp.complete();
        } else {
            return false;
        }
    }

    /**
     * Enables / disables the OK and Choose all button depending on whether or not the currently
     * chosen merge rule instance is applicable.
     */
    private void checkApplicable() {
        okButton.setEnabled(chosenGoals.size() > 0
                && isApplicableForCandidates(immutableListFromIterabe(chosenGoals)));

        chooseAllButton.setEnabled(candidates.size() > 0
                && isApplicableForCandidates(immutableListFromIterabe(candidates)));

        txtDistForm.setEnabled(candidates.size() == 1 || chosenGoals.size() == 1);
        if (!txtDistForm.isEnabled()) {
            chosenDistForm = null;
        }
    }

    /**
     * Checks whether the selected distinguishable formula is actually suitable for this purpose.
     *
     * @return true iff the chosen "distinguishing formula" is a distinguishing formula.
     */
    private boolean isSuitableDistFormula() {
        if (chosenDistForm == null) {
            return false;
        }

        // The formula should be provable for the first state
        // whilst its complement should be provable for the second state.

        final TermBuilder tb = services.getTermBuilder();

        final Goal partnerGoal = candidates.size() == 1 ? candidates.getFirst().getGoal()
                : (chosenGoals.size() == 1 ? chosenGoals.first().getGoal() : null);

        if (partnerGoal == null) {
            return false;
        }

        return checkProvability(mergeGoalPio.first.sequent(), chosenDistForm, services)
                && checkProvability(partnerGoal.sequent(), tb.not(chosenDistForm), services);
    }

    /**
     * Checks whether the given formula can be proven within the given sequent.
     *
     * @param seq Sequent in which to check the provability of formulaToProve.
     * @param formulaToProve Formula to prove.
     * @return True iff formulaToProve can be proven within the given sequent.
     */
    private static boolean checkProvability(Sequent seq, Term formulaToProve, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        Semisequent antecedent = seq.antecedent();

        for (SequentFormula succedentFormula : seq.succedent()) {
            if (!succedentFormula.formula().containsJavaBlockRecursive()) {
                antecedent =
                    antecedent.insertFirst(new SequentFormula(tb.not(succedentFormula.formula())))
                            .semisequent();
            }
        }

        return MergeRuleUtils.isProvable(
            Sequent.createSequent(antecedent, new Semisequent(new SequentFormula(formulaToProve))),
            services, 1000);
    }

    /**
     * @param it Iterable to convert into an ImmutableList.
     * @return An ImmutableList consisting of the elements in it.
     */
    private <T> ImmutableList<T> immutableListFromIterabe(Iterable<T> it) {
        ImmutableList<T> result = ImmutableSLList.nil();
        for (T t : it) {
            result = result.prepend(t);
        }
        return result;
    }

    /**
     * @return The candidate chosen at the moment (by the combo box).
     */
    private MergePartner getSelectedCandidate() {
        return getNthCandidate(cmbCandidates.getSelectedIndex());
    }

    /**
     * Returns the n-th candidate in the list.
     *
     * @param n Index of the merge candidate.
     * @return The n-th candidate in the list.
     */
    private MergePartner getNthCandidate(int n) {
        int i = 0;
        for (MergePartner elem : candidates) {
            if (i == n) {
                return elem;
            }
            i++;
        }

        return null;
    }

    /**
     * Loads the merge candidates into the combo box, initializes the partner editor pane with the
     * text of the first candidate.
     */
    private void loadCandidates() {
        if (candidates.size() < 1) {
            return;
        }

        for (MergePartner candidate : candidates) {
            cmbCandidates.addItem("Node " + candidate.getGoal().node().serialNr());
        }

        setHighlightedSequentForArea(candidates.getFirst().getGoal(),
            candidates.getFirst().getPio(), txtPartner2);

        checkApplicable();
    }

    /**
     * Adds the given goal to the given editor pane, with the portion that corresponds to the given
     * position highlighted in bold.
     *
     * @param goal Goal to add.
     * @param pio Position indicating subterm to highlight.
     * @param area The editor pane to add the highlighted goal to.
     */
    private void setHighlightedSequentForArea(Goal goal, PosInOccurrence pio, JEditorPane area) {

        String subterm = LogicPrinter.quickPrintTerm(pio.subTerm(), services);

        // Render subterm to highlight as a regular expression.
        // Note: Four backslashs in replacement expression will result in
        // one backslash in the resulting string.
        subterm = subterm.replaceAll("\\s", "\\\\s");
        subterm = subterm.replaceAll("(\\\\s)+", "\\\\E\\\\s*\\\\Q");
        subterm = "\\Q" + subterm + "\\E";
        if (subterm.endsWith("\\Q\\E")) {
            subterm = subterm.substring(0, subterm.length() - 4);
        }

        // Find a match
        String sequent = LogicPrinter.quickPrintSequent(goal.sequent(), services);
        Pattern p = Pattern.compile(subterm);
        Matcher m = p.matcher(sequent);

        // Original sequent (without highlighted text) as fallback
        String newText = sequent;

        // Escape HTML characters
        newText = LogicPrinter.escapeHTML(newText, true);

        if (m.find()) {
            // Assemble new text
            String before = LogicPrinter.escapeHTML(sequent.substring(0, m.start() - 1), true);
            String main = "<b>"
                + LogicPrinter.escapeHTML(sequent.substring(m.start(), m.end()), true) + "</b>";
            String after = LogicPrinter.escapeHTML(sequent.substring(m.end()), true);

            newText = before + main + after;
        }

        // Treat spaces and newlines: Are ignored in HTML text area
        newText = newText.replace("\n", "<br>");
        newText = newText.replace(" ", "&nbsp;");

        area.setText(newText);

    }

}
