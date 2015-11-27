// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.joinrule;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.AbstractButton;
import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JEditorPane;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.border.TitledBorder;
import javax.swing.text.html.HTMLDocument;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.utilities.WrapLayout;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.join.JoinProcedure;
import de.uka.ilkd.key.rule.join.JoinRule;
import de.uka.ilkd.key.rule.join.JoinRuleBuiltInRuleApp;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * JDialog for selecting a subset of candidate goals as partners for a join rule
 * application.
 * 
 * @author Dominic Scheurer
 */
public class JoinPartnerSelectionDialog extends JDialog {

    private static final long serialVersionUID = -1460097562546341922L;

    /** The tooltip hint for the checkbox. */
    private static final String CB_SELECT_CANDIDATE_HINT =
            "Select to add shown state as a join partner.";

    /** The tooltip for the OK button */
    private static final String CHOOSE_ALL_BTN_TOOLTIP_TXT =
            "Select all proposed goals as join partners. "
                    + "Only enabled if the join is applicable for all goals and the chosen join procedure.";
    /** The tooltip for the choose-all button */
    private static final String OK_BTN_TOOLTIP_TXT =
            "Select the chosen goals as join partners. "
                    + "Only enabled if at least one goal is chosen and the join is applicable for the "
                    + "chosen goals and join procedure.";

    /** The initial size of this dialog. */
    private static final Dimension INITIAL_SIZE = new Dimension(850, 450);

    /**
     * The font for the JEditorPanes. Should resemble the standard font of KeY
     * for proofs etc.
     */
    private static final Font TXT_AREA_FONT = new Font(Font.MONOSPACED,
            Font.PLAIN, 14);

    private final static MainWindow MAIN_WINDOW_INSTANCE = MainWindow
            .getInstance();

    /** Comparator for goals; sorts by serial nr. of the node */
    private static Comparator<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> GOAL_COMPARATOR =
            new Comparator<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>>() {
                @Override
                public int compare(
                        Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> o1,
                        Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> o2) {
                    return o1.first.node().serialNr()
                            - o2.first.node().serialNr();
                }
            };

    private LinkedList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> candidates =
            null;
    private Services services = null;
    private Pair<Goal, PosInOccurrence> joinGoalPio = null;

    /** The chosen goals. */
    private SortedSet<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> chosenGoals =
            new TreeSet<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>>(
                    GOAL_COMPARATOR);

    /** The chosen join method. */
    private JoinProcedure chosenRule = JoinProcedure.getJoinProcedures().head();

    /** The chosen distinguishing formula */
    private Term chosenDistForm = null;

    private JEditorPane txtPartner1 = null;
    private JEditorPane txtPartner2 = null;
    private JComboBox<String> cmbCandidates = null;
    private JCheckBox cbSelectCandidate = null;
    private ButtonGroup bgJoinMethods = null;
    private final JTextField txtDistForm;

    private JScrollPane scrpPartner1 = null;
    private JScrollPane scrpPartner2 = null;

    private JButton okButton = null;
    private JButton chooseAllButton = null;

    private JoinPartnerSelectionDialog() {
        super(MAIN_WINDOW_INSTANCE, "Select partner node for join operation",
                true);

        setLocation(MAIN_WINDOW_INSTANCE.getLocation());

        // Text areas for goals to join
        txtPartner1 = new JEditorPane();
        txtPartner2 = new JEditorPane();
        for (JEditorPane jep : new JEditorPane[] { txtPartner1, txtPartner2 }) {
            jep.setEditable(false);
            jep.setContentType("text/html");

            // Set font
            String cssRule =
                    "body { font-family: " + TXT_AREA_FONT.getFamily() + "; "
                            + "font-size: " + TXT_AREA_FONT.getSize() + "pt; }";
            ((HTMLDocument) jep.getDocument()).getStyleSheet().addRule(cssRule);
        }

        scrpPartner1 = new JScrollPane(txtPartner1);
        scrpPartner2 = new JScrollPane(txtPartner2);

        // Goal selection dropdown field and checkbox
        cmbCandidates = new JComboBox<String>();
        cmbCandidates.setMaximumSize(new Dimension(Integer.MAX_VALUE, 20));
        cmbCandidates.addItemListener(new ItemListener() {
            @Override
            public void itemStateChanged(ItemEvent e) {
                Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> selectedCandidate =
                        getSelectedCandidate();

                setHighlightedSequentForArea(selectedCandidate.first,
                        selectedCandidate.second, txtPartner2);

                if (chosenGoals.contains(selectedCandidate)) {
                    cbSelectCandidate.setSelected(true);
                }
                else {
                    cbSelectCandidate.setSelected(false);
                }
            }
        });

        addComponentListener(new ComponentAdapter() {
            @Override
            public void componentResized(ComponentEvent e) {
                super.componentResized(e);

                int halfWidth = getWidth() / 2;
                scrpPartner1.setPreferredSize(new Dimension(halfWidth,
                        scrpPartner1.getHeight()));
                scrpPartner2.setPreferredSize(new Dimension(halfWidth,
                        scrpPartner2.getHeight()));
            }
        });

        cbSelectCandidate = new JCheckBox();
        cbSelectCandidate.setToolTipText(CB_SELECT_CANDIDATE_HINT);
        cbSelectCandidate.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                if (cbSelectCandidate.isSelected()) {
                    chosenGoals.add(getSelectedCandidate());
                }
                else {
                    chosenGoals.remove(getSelectedCandidate());
                }

                checkApplicable();
            }
        });

        bgJoinMethods = new ButtonGroup();
        for (final JoinProcedure rule : JoinProcedure.getJoinProcedures()) {
            JRadioButton rb = new JRadioButton(rule.toString());
            rb.setSelected(true);

            rb.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    chosenRule = rule;

                    checkApplicable();
                }
            });
            bgJoinMethods.add(rb);
        }

        // Join state container
        JPanel joinStateContainer = new JPanel();
        joinStateContainer.setLayout(new BoxLayout(joinStateContainer,
                BoxLayout.Y_AXIS));
        joinStateContainer.add(scrpPartner1);

        TitledBorder joinStateContainerTitle =
                BorderFactory.createTitledBorder("State to join");
        joinStateContainerTitle.setTitleJustification(TitledBorder.LEFT);
        joinStateContainer.setBorder(joinStateContainerTitle);

        // Join partner container
        JPanel partnerContainer = new JPanel();
        partnerContainer.setLayout(new BoxLayout(partnerContainer,
                BoxLayout.Y_AXIS));
        partnerContainer.add(scrpPartner2);

        JPanel selectionContainer = new JPanel();
        selectionContainer.setLayout(new BoxLayout(selectionContainer,
                BoxLayout.X_AXIS));
        selectionContainer.add(cbSelectCandidate);
        selectionContainer.add(cmbCandidates);

        partnerContainer.add(selectionContainer);

        TitledBorder txtPartner2Title =
                BorderFactory.createTitledBorder("Potential join partners");
        txtPartner2Title.setTitleJustification(TitledBorder.LEFT);
        partnerContainer.setBorder(txtPartner2Title);

        // Upper container
        JPanel upperContainer = new JPanel();
        upperContainer
                .setLayout(new BoxLayout(upperContainer, BoxLayout.X_AXIS));
        upperContainer.add(joinStateContainer);
        upperContainer.add(partnerContainer);

        // Join rules container
        JPanel joinRulesContainer = new JPanel();
        joinRulesContainer.setLayout(new WrapLayout());

        for (Enumeration<AbstractButton> e = bgJoinMethods.getElements(); e
                .hasMoreElements();) {
            JRadioButton rb = (JRadioButton) e.nextElement();
            joinRulesContainer.add(rb);
        }

        TitledBorder joinRulesContainerTitle =
                BorderFactory.createTitledBorder("Concrete join rule to apply");
        joinRulesContainerTitle.setTitleJustification(TitledBorder.LEFT);
        joinRulesContainerTitle.setBorder(joinStateContainerTitle);
        joinRulesContainer.setBorder(joinRulesContainerTitle);

        // Distinguishing method input field container
        txtDistForm = new JTextField();
        txtDistForm.setMargin(new Insets(5, 0, 5, 0));
        txtDistForm.addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                chosenDistForm =
                        JoinRuleUtils.translateToFormula(services,
                                txtDistForm.getText());

                if (chosenDistForm == null || !isSuitableDistFormula()) {
                    txtDistForm.setForeground(Color.RED);
                }
                else {
                    txtDistForm.setForeground(Color.BLACK);
                }

                checkApplicable();
            }
        });

        JPanel distFormContainer = new JPanel();
        distFormContainer.setLayout(new BorderLayout());

        distFormContainer.add(txtDistForm, BorderLayout.CENTER);

        TitledBorder distFormContainerTitle =
                BorderFactory
                        .createTitledBorder("Distinguishing formula (leave empty for automatic generation!)");
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

        okButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
                dispose();
            }
        });

        chooseAllButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> candidate : candidates) {
                    chosenGoals.add(candidate);
                }
                setVisible(false);
            }
        });

        cancelButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                chosenGoals = null;
                setVisible(false);
            }
        });

        JPanel ctrlBtnsContainer = new JPanel();
        ctrlBtnsContainer.setLayout(new BoxLayout(ctrlBtnsContainer,
                BoxLayout.X_AXIS));
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
        lowerContainer
                .setLayout(new BoxLayout(lowerContainer, BoxLayout.Y_AXIS));
        lowerContainer.add(joinRulesContainer);
        lowerContainer.add(new Box.Filler(verticalFillerDim, verticalFillerDim,
                verticalFillerDim));
        lowerContainer.add(distFormContainer);
        lowerContainer.add(new Box.Filler(verticalFillerDim, verticalFillerDim,
                verticalFillerDim));
        lowerContainer.add(ctrlBtnsContainer);

        // Add components to content pane
        getContentPane().add(upperContainer, BorderLayout.CENTER);
        getContentPane().add(lowerContainer, BorderLayout.SOUTH);

        setSize(INITIAL_SIZE);
    }

    public static void main(String[] args) {
        JoinPartnerSelectionDialog diag = new JoinPartnerSelectionDialog();
        diag.setVisible(true);
    }

    /**
     * Creates a new join partner selection dialog.
     * 
     * @param joinGoal
     *            The first (already chosen) join partner.
     * @param pio
     *            Position of Update-Modality-Postcondition formula in the
     *            joinNode.
     * @param candidates
     *            Potential join candidates.
     * @param services
     *            The services object.
     */
    public JoinPartnerSelectionDialog(
            Goal joinGoal,
            PosInOccurrence pio,
            ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> candidates,
            Services services) {

        this();
        this.services = services;

        this.candidates =
                new LinkedList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>>();
        this.joinGoalPio = new Pair<Goal, PosInOccurrence>(joinGoal, pio);

        for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> candidate : candidates) {
            int insPos =
                    Collections.binarySearch(this.candidates, candidate,
                            GOAL_COMPARATOR);

            insPos = (insPos + 1) * -1;
            this.candidates.add(insPos, candidate);
        }

        setHighlightedSequentForArea(joinGoal, pio, txtPartner1);
        loadCandidates();

    }

    /**
     * @return All chosen join partners.
     */
    public ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> getChosenCandidates() {
        ImmutableSLList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> result =
                ImmutableSLList.nil();

        if (chosenGoals != null) {
            return result.append(chosenGoals);
        }
        else {
            return result;
        }
    }

    /**
     * @param <T>
     * @return The chosen join rule.
     */
    @SuppressWarnings("unchecked")
    public <T extends JoinProcedure> T getChosenJoinRule() {
        JoinProcedureCompletion<T> completion =
                (JoinProcedureCompletion<T>) JoinProcedureCompletion
                        .getCompletionForClass(chosenRule.getClass());

        return completion.complete((T) chosenRule, joinGoalPio.first);
    }

    /**
     * @return The chosen distinguishing formula. If null, an automatic
     *         generation of the distinguishing formula should be performed.
     */
    public Term getChosenDistinguishingFormula() {
        return isSuitableDistFormula() ? chosenDistForm : null;
    }

    /**
     * Checks whether the join rule is applicable for the given set of
     * candidates.
     *
     * @param theCandidates
     *            Candidates to instantiate the join rule application with.
     * @return true iff the join rule instance induced by the given set of
     *         candidates is applicable.
     */
    private boolean isApplicableForCandidates(
            ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> theCandidates) {
        if (joinGoalPio != null && candidates != null && chosenRule != null) {
            JoinRuleBuiltInRuleApp joinRuleApp =
                    (JoinRuleBuiltInRuleApp) JoinRule.INSTANCE.createApp(
                            joinGoalPio.second, services);

            joinRuleApp.setJoinNode(joinGoalPio.first.node());
            joinRuleApp.setConcreteRule(chosenRule);
            joinRuleApp.setJoinPartners(theCandidates);

            return joinRuleApp.complete();
        }
        else {
            return false;
        }
    }

    /**
     * Enables / disables the OK and Choose all button depending on whether or
     * not the currently chosen join rule instance is applicable.
     */
    private void checkApplicable() {
        okButton.setEnabled(chosenGoals.size() > 0
                && isApplicableForCandidates(immutableListFromIterabe(chosenGoals)));

        chooseAllButton
                .setEnabled(candidates.size() > 0
                        && isApplicableForCandidates(immutableListFromIterabe(candidates)));

        txtDistForm.setEnabled(candidates.size() == 1
                || chosenGoals.size() == 1);
        if (!txtDistForm.isEnabled()) {
            chosenDistForm = null;
        }
    }

    /**
     * Checks whether the selected distinguishable formula is actually suitable
     * for this purpose.
     * 
     * @return true iff the chosen "distinguishing formula" is a distinguishing
     *         formula.
     */
    private boolean isSuitableDistFormula() {
        if (chosenDistForm == null) {
            return false;
        }

        // The formula should be provable for the first state
        // whilst its complement should be provable for the second state.

        final TermBuilder tb = services.getTermBuilder();

        final Goal partnerGoal =
                candidates.size() == 1 ? candidates.getFirst().first
                        : (chosenGoals.size() == 1 ? chosenGoals.first().first
                                : null);

        if (partnerGoal == null) {
            return false;
        }

        return checkProvability(joinGoalPio.first.sequent(), chosenDistForm,
                services)
                && checkProvability(partnerGoal.sequent(),
                        tb.not(chosenDistForm), services);
    }

    /**
     * Checks whether the given formula can be proven within the given sequent.
     *
     * @param seq
     *            Sequent in which to check the provability of formulaToProve.
     * @param formulaToProve
     *            Formula to prove.
     * @return True iff formulaToProve can be proven within the given sequent.
     */
    private static boolean checkProvability(Sequent seq, Term formulaToProve,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        Semisequent antecedent = seq.antecedent();

        for (SequentFormula succedentFormula : seq.succedent()) {
            if (!succedentFormula.formula().isContainsJavaBlockRecursive()) {
                antecedent =
                        antecedent.insertFirst(
                                new SequentFormula(tb.not(succedentFormula
                                        .formula()))).semisequent();
            }
        }

        if (!JoinRuleUtils.isProvable(Sequent.createSequent(antecedent,
                new Semisequent(new SequentFormula(formulaToProve))), services,
                1000)) {
            return false;
        }

        return true;
    }

    /**
     * @param it
     *            Iterable to convert into an ImmutableList.
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
    private Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> getSelectedCandidate() {
        return getNthCandidate(cmbCandidates.getSelectedIndex());
    }

    /**
     * Returns the n-th candidate in the list.
     * 
     * @param n
     *            Index of the join candidate.
     * @return The n-th candidate in the list.
     */
    private Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> getNthCandidate(
            int n) {
        int i = 0;
        for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> elem : candidates) {
            if (i == n) {
                return elem;
            }
            i++;
        }

        return null;
    }

    /**
     * Loads the join candidates into the combo box, initializes the partner
     * editor pane with the text of the first candidate.
     */
    private void loadCandidates() {
        if (candidates.size() < 1) {
            return;
        }

        for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> candidate : candidates) {
            cmbCandidates.addItem("Node " + candidate.first.node().serialNr());
        }

        setHighlightedSequentForArea(candidates.getFirst().first,
                candidates.getFirst().second, txtPartner2);

        checkApplicable();
    }

    /**
     * Adds the given goal to the given editor pane, with the portion that
     * corresponds to the given position highlighted in bold.
     * 
     * @param goal
     *            Goal to add.
     * @param pio
     *            Position indicating subterm to highlight.
     * @param area
     *            The editor pane to add the highlighted goal to.
     */
    private void setHighlightedSequentForArea(Goal goal, PosInOccurrence pio,
            JEditorPane area) {

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
        String sequent =
                LogicPrinter.quickPrintSequent(goal.sequent(), services);
        Pattern p = Pattern.compile(subterm);
        Matcher m = p.matcher(sequent);

        // Original sequent (without highlighted text) as fallback
        String newText = sequent;

        // Escape HTML characters
        newText = LogicPrinter.escapeHTML(newText, true);

        if (m.find()) {
            // Assemble new text
            String before =
                    LogicPrinter.escapeHTML(
                            sequent.substring(0, m.start() - 1), true);
            String main =
                    "<b>"
                            + LogicPrinter
                                    .escapeHTML(
                                            sequent.substring(m.start(),
                                                    m.end()), true) + "</b>";
            String after =
                    LogicPrinter.escapeHTML(sequent.substring(m.end()), true);

            newText = before + main + after;
        }

        // Treat spaces and newlines: Are ignored in HTML text area
        newText = newText.replace("\n", "<br>");
        newText = newText.replace(" ", "&nbsp;");

        area.setText(newText);

    }

}
