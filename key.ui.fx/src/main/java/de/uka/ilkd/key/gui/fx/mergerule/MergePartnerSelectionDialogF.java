/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.mergerule;

import java.util.Collections;
import java.util.Comparator;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleGroup;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.scene.text.Font;
import javafx.scene.text.FontWeight;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.Nullable;

/**
 * Dialog for selecting a subset of candidate goals as partners for a {@link MergeRule}
 * application.
 * <p>
 * Port of the Swing {@code de.uka.ilkd.key.gui.mergerule.MergePartnerSelectionDialog} (key.ui):
 * the two monospaced sequent panes (with the focus subterm rendered in bold instead of the
 * Swing {@code <b>} HTML markup), the candidate combo box with the "select as merge partner"
 * checkbox, the radio buttons per {@link MergeProcedure}, and the distinguishing-formula field
 * with live parse validation (red style class instead of a red foreground) and the identical
 * OK/Choose-All enablement logic ({@code checkApplicable}) and suitability check
 * ({@code isSuitableDistFormula}). Cancel leaves the chosen goals null so that the completion
 * returns null (rule silently skipped, as in the Swing UI).
 * <p>
 * Note: fetching the chosen merge rule via {@link #getChosenMergeRule()} may open the nested
 * {@link AbstractionPredicatesChoiceDialogF} when the predicate-abstraction procedure was
 * chosen — the nested modal call happens after {@link #show()} returns, exactly as in Swing
 * (where the dialog was evaluated after {@code setVisible(true)} returned on the EDT).
 *
 * @author Dominic Scheurer (original Swing dialog)
 */
public final class MergePartnerSelectionDialogF {

    /** The tooltip hint for the checkbox. */
    private static final String CB_SELECT_CANDIDATE_HINT =
        "Select to add shown state as a merge partner.";

    /** The tooltip for the Choose-All button (Swing constant, order swapped there). */
    private static final String CHOOSE_ALL_BTN_TOOLTIP_TXT =
        "Select all proposed goals as merge partners. "
            + "Only enabled if the merge is applicable for all goals and the chosen merge procedure.";
    /** The tooltip for the OK button */
    private static final String OK_BTN_TOOLTIP_TXT = "Select the chosen goals as merge partners. "
        + "Only enabled if at least one goal is chosen and the merge is applicable for the "
        + "chosen goals and merge procedure.";

    /** The initial size of this dialog. */
    private static final double INITIAL_WIDTH = 900;
    private static final double INITIAL_HEIGHT = 450;

    /**
     * The font for the sequent panes. Should resemble the standard font of KeY for proofs etc.
     */
    private static final Font TXT_AREA_FONT = Font.font("Monospaced", FontWeight.NORMAL, 14);
    private static final Font TXT_AREA_FONT_BOLD = Font.font("Monospaced", FontWeight.BOLD, 14);

    /** Comparator for goals; sorts by serial nr. of the node (Swing GOAL_COMPARATOR). */
    private static final Comparator<MergePartner> GOAL_COMPARATOR =
        Comparator.comparingInt(o -> o.getGoal().node().serialNr());

    private final Stage stage = new Stage();

    private final SortedSet<MergePartner> candidates = new TreeSet<>(GOAL_COMPARATOR);
    @Nullable
    private Services services = null;
    @Nullable
    private Pair<Goal, PosInOccurrence> mergeGoalPio = null;

    /** The chosen goals. Null after cancel (Swing semantics: completion returns null). */
    @Nullable
    private SortedSet<MergePartner> chosenGoals = new TreeSet<>(GOAL_COMPARATOR);

    /** The chosen merge method. Head of {@link MergeProcedure#getMergeProcedures()}. */
    private MergeProcedure chosenRule = MergeProcedure.getMergeProcedures().head();

    /** The chosen distinguishing formula */
    @Nullable
    private JTerm chosenDistForm = null;

    private final TextFlow sequent1Flow = new TextFlow();
    private final TextFlow sequent2Flow = new TextFlow();
    private final ComboBox<String> cmbCandidates = new ComboBox<>();
    private final CheckBox cbSelectCandidate = new CheckBox();
    private final TextField txtDistForm = new TextField();
    private final Button okButton = new Button("OK");
    private final Button chooseAllButton = new Button("Choose All");

    /**
     * Creates a new merge partner selection dialog.
     *
     * @param mergeGoal The first (already chosen) merge partner.
     * @param pio Position of Update-Modality-Postcondition formula in the mergeNode.
     * @param candidates Potential merge candidates.
     * @param services The services object.
     * @param owner the owner window for the modal dialog (may be null)
     */
    public MergePartnerSelectionDialogF(Goal mergeGoal,
            PosInOccurrence pio,
            ImmutableList<MergePartner> candidates, Services services,
            @Nullable Window owner) {
        this.services = services;

        stage.setTitle("Select partner node for merge operation");

        this.mergeGoalPio = new Pair<>(mergeGoal, pio);

        // the Swing original inserts into a LinkedList with binary search — same result:
        // candidates sorted by node serial number
        for (MergePartner candidate : candidates) {
            this.candidates.add(candidate);
        }

        BorderPane root = createContent();

        if (owner != null) {
            stage.initOwner(owner);
        }
        stage.initModality(owner != null ? Modality.WINDOW_MODAL : Modality.APPLICATION_MODAL);
        Scene scene = new Scene(root, INITIAL_WIDTH, INITIAL_HEIGHT);
        ThemeManager.getInstance().style(scene);
        stage.setScene(scene);

        setHighlightedSequentForArea(mergeGoal, pio, sequent1Flow);
        loadCandidates();
    }

    private BorderPane createContent() {
        // ---- upper container: state to merge | potential merge partners ----
        Label seq1Title = new Label("State to merge");
        seq1Title.getStyleClass().add("dialog-section-title");
        VBox mergeStateContainer =
            new VBox(2, seq1Title, wrapScrollable(sequent1Flow, "join-sequent-view"));

        Label seq2Title = new Label("Potential merge partners");
        seq2Title.getStyleClass().add("dialog-section-title");

        cbSelectCandidate.setTooltip(new Tooltip(CB_SELECT_CANDIDATE_HINT));
        cbSelectCandidate.setOnAction(e -> {
            MergePartner selected = getSelectedCandidate();
            if (selected == null) {
                return;
            }
            if (cbSelectCandidate.isSelected()) {
                chosenGoals.add(selected);
            } else {
                chosenGoals.remove(selected);
            }
            checkApplicable();
        });

        cmbCandidates.setMaxWidth(Double.MAX_VALUE);
        cmbCandidates.valueProperty().addListener((obs, oldV, newV) -> {
            MergePartner selectedCandidate = getSelectedCandidate();
            if (selectedCandidate == null) {
                return;
            }
            setHighlightedSequentForArea(selectedCandidate.getGoal(),
                selectedCandidate.getPio(), sequent2Flow);
            cbSelectCandidate.setSelected(chosenGoals.contains(selectedCandidate));
        });

        HBox selectionContainer = new HBox(6, cbSelectCandidate, cmbCandidates);
        HBox.setHgrow(cmbCandidates, Priority.ALWAYS);
        VBox partnerContainer =
            new VBox(2, seq2Title, wrapScrollable(sequent2Flow, "join-sequent-view"),
                selectionContainer);
        VBox.setVgrow(partnerContainer.getChildren().get(1), Priority.ALWAYS);

        HBox upperContainer = new HBox(10, mergeStateContainer, partnerContainer);
        HBox.setHgrow(mergeStateContainer, Priority.ALWAYS);
        HBox.setHgrow(partnerContainer, Priority.ALWAYS);
        upperContainer.setPadding(new Insets(8));

        // ---- lower container: merge rules, dist formula, buttons ----
        ToggleGroup bgMergeMethods = new ToggleGroup();
        HBox mergeRulesContainer = new HBox(10);
        mergeRulesContainer.setPadding(new Insets(6, 0, 6, 0));
        for (final MergeProcedure rule : MergeProcedure.getMergeProcedures()) {
            RadioButton rb = new RadioButton(rule.toString());
            rb.setToggleGroup(bgMergeMethods);
            rb.setSelected(rule == chosenRule);
            rb.setOnAction(e -> {
                chosenRule = rule;
                checkApplicable();
            });
            mergeRulesContainer.getChildren().add(rb);
        }

        txtDistForm.setPromptText(
            "Distinguishing formula (leave empty for automatic generation!)");
        txtDistForm.textProperty().addListener((obs, oldV, newText) -> {
            chosenDistForm = MergeRuleUtils.translateToFormula(services, newText);

            if (chosenDistForm == null || !isSuitableDistFormula()) {
                txtDistForm.getStyleClass().add("join-input-error");
            } else {
                txtDistForm.getStyleClass().remove("join-input-error");
            }
            checkApplicable();
        });

        okButton.setDefaultButton(true);
        okButton.setTooltip(new Tooltip(OK_BTN_TOOLTIP_TXT));
        okButton.setOnAction(e -> stage.close());

        chooseAllButton.setTooltip(new Tooltip(CHOOSE_ALL_BTN_TOOLTIP_TXT));
        chooseAllButton.setOnAction(e -> {
            chosenGoals.addAll(candidates);
            stage.close();
        });

        Button cancelButton = new Button("Cancel");
        cancelButton.setCancelButton(true);
        cancelButton.setOnAction(e -> {
            chosenGoals = null; // Swing: cancel => getChosenCandidates yields nil
            stage.close();
        });

        HBox ctrlBtnsContainer = new HBox(20, okButton, chooseAllButton, cancelButton);
        ctrlBtnsContainer.setAlignment(Pos.CENTER);
        ctrlBtnsContainer.setPadding(new Insets(8, 0, 8, 0));

        Label mergeRulesTitle = new Label("Concrete merge procedure to apply");
        mergeRulesTitle.getStyleClass().add("dialog-section-title");
        Label distFormTitle = new Label("Distinguishing formula");
        distFormTitle.getStyleClass().add("dialog-section-title");

        VBox lowerContainer = new VBox(6, mergeRulesTitle, mergeRulesContainer, distFormTitle,
            txtDistForm, ctrlBtnsContainer);
        lowerContainer.setPadding(new Insets(4, 8, 8, 8));

        BorderPane root = new BorderPane();
        root.setCenter(upperContainer);
        root.setBottom(lowerContainer);
        return root;
    }

    private ScrollPane wrapScrollable(TextFlow flow, String styleClass) {
        flow.getStyleClass().add(styleClass);
        ScrollPane pane = new ScrollPane(flow);
        pane.setFitToWidth(true);
        pane.setHbarPolicy(ScrollPane.ScrollBarPolicy.AS_NEEDED);
        VBox.setVgrow(pane, Priority.ALWAYS);
        return pane;
    }

    /**
     * Shows the dialog modally and blocks until it is closed (Swing: {@code setVisible(true)} on
     * the modal JDialog, called on the EDT).
     */
    public void show() {
        stage.showAndWait();
    }

    // joinmerge: test support for the key.fx.verify.joinmerge self test — non-blocking show,
    // programmatic cancel, and control accessors with the same semantics as the buttons; the
    // production path uses show().

    /** Shows the dialog without blocking (self-test support; parity with {@link #show()}). */
    public void showNonBlocking() {
        stage.show();
    }

    /** Confirms the dialog if the OK button is enabled (self-test support). */
    public void requestOk() {
        if (!okButton.isDisabled()) {
            stage.close();
        }
    }

    /** Cancels the dialog (self-test support; parity with the cancel button). */
    public void requestCancel() {
        chosenGoals = null; // Swing: cancel => getChosenCandidates yields nil
        stage.close();
    }

    /** Exposes the dialog stage for tests. */
    public Stage getStageForVerification() {
        return stage;
    }

    /** Exposes the candidate combo box for tests. */
    public ComboBox<String> getCmbCandidates() {
        return cmbCandidates;
    }

    /** Exposes the partner selection checkbox for tests. */
    public CheckBox getCbSelectCandidate() {
        return cbSelectCandidate;
    }

    /** Exposes the distinguishing-formula field for tests. */
    public TextField getTxtDistForm() {
        return txtDistForm;
    }

    /** Exposes the OK button for tests. */
    public Button getOkButton() {
        return okButton;
    }

    /** Exposes the Choose-All button for tests. */
    public Button getChooseAllButton() {
        return chooseAllButton;
    }

    /** Exposes the "State to merge" sequent flow for tests. */
    public TextFlow getSequent1Flow() {
        return sequent1Flow;
    }

    /** Exposes the partner sequent flow for tests. */
    public TextFlow getSequent2Flow() {
        return sequent2Flow;
    }

    /**
     * @return All chosen merge partners (empty iff cancelled — Swing
     *         {@code getChosenCandidates}).
     */
    public ImmutableList<MergePartner> getChosenCandidates() {
        ImmutableList<MergePartner> result = ImmutableList.nil();
        if (chosenGoals != null) {
            return result.append(chosenGoals);
        } else {
            return result;
        }
    }

    /**
     * @param <T> the concrete merge procedure type
     * @return The chosen merge rule. May open the nested procedure completion dialog (see class
     *         javadoc).
     */
    @SuppressWarnings("unchecked")
    public <T extends MergeProcedure> T getChosenMergeRule() {
        MergeProcedureCompletionF<T> completion =
            (MergeProcedureCompletionF<T>) MergeProcedureCompletionF
                    .getCompletionForClass(chosenRule.getClass());

        return completion.complete((T) chosenRule, mergeGoalPio,
            chosenGoals == null ? Collections.emptyList() : chosenGoals);
    }

    /**
     * @return The chosen distinguishing formula. If null, an automatic generation of the
     *         distinguishing formula should be performed.
     */
    public @Nullable JTerm getChosenDistinguishingFormula() {
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
        if (mergeGoalPio != null && services != null && chosenRule != null) {
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
     * Enables / disables the OK and Choose-all button depending on whether or not the currently
     * chosen merge rule instance is applicable (Swing {@code checkApplicable}).
     */
    private void checkApplicable() {
        okButton.setDisable(
            chosenGoals.isEmpty()
                    || !isApplicableForCandidates(immutableListFromIterable(chosenGoals)));

        chooseAllButton.setDisable(
            candidates.isEmpty()
                    || !isApplicableForCandidates(immutableListFromIterable(candidates)));

        txtDistForm.setDisable(!(candidates.size() == 1 || chosenGoals.size() == 1));
        if (txtDistForm.isDisabled()) {
            chosenDistForm = null;
        }
    }

    /**
     * Checks whether the selected distinguishing formula is actually suitable for this purpose
     * (Swing {@code isSuitableDistFormula}).
     *
     * @return true iff the chosen "distinguishing formula" is a distinguishing formula.
     */
    private boolean isSuitableDistFormula() {
        if (chosenDistForm == null) {
            return false;
        }

        // The formula should be provable for the first state
        // whilst its complement should be provable for the second state.

        final var tb = services.getTermBuilder();

        final Goal partnerGoal = candidates.size() == 1 ? candidates.getFirst().getGoal()
                : (chosenGoals.size() == 1 ? chosenGoals.first().getGoal() : null);

        if (partnerGoal == null) {
            return false;
        }

        return checkProvability(mergeGoalPio.first.sequent(), chosenDistForm, services)
                && checkProvability(partnerGoal.sequent(), tb.not(chosenDistForm), services);
    }

    /**
     * Checks whether the given formula can be proven within the given sequent (Swing
     * {@code checkProvability}, unchanged).
     *
     * @param seq Sequent in which to check the provability of formulaToProve.
     * @param formulaToProve Formula to prove.
     * @return True iff formulaToProve can be proven within the given sequent.
     */
    private static boolean checkProvability(Sequent seq, JTerm formulaToProve, Services services) {
        final var tb = services.getTermBuilder();

        Sequent toProve = JavaDLSequentKit.createSequent(seq.antecedent().asList(),
            ImmutableList.singleton(new SequentFormula(formulaToProve)));

        for (SequentFormula succedentFormula : seq.succedent()) {
            final JTerm formula = (JTerm) succedentFormula.formula();
            if (!formula.containsJavaBlockRecursive()) {
                toProve =
                    toProve.addFormula(new SequentFormula(tb.not(formula)), true, true).sequent();
            }
        }

        return MergeRuleUtils.isProvable(toProve, services, 1000);
    }

    /**
     * @param it Iterable to convert into an ImmutableList (Swing
     *        {@code immutableListFromIterabe}).
     * @return An ImmutableList consisting of the elements in it.
     */
    private static <T> ImmutableList<T> immutableListFromIterable(Iterable<T> it) {
        ImmutableList<T> result = ImmutableList.nil();
        for (T t : it) {
            result = result.prepend(t);
        }
        return result;
    }

    /**
     * @return The candidate chosen at the moment (by the combo box).
     */
    private @Nullable MergePartner getSelectedCandidate() {
        return getNthCandidate(cmbCandidates.getSelectionModel().getSelectedIndex());
    }

    /**
     * Returns the n-th candidate in the list (Swing {@code getNthCandidate}).
     *
     * @param n Index of the merge candidate.
     * @return The n-th candidate in the list, or null.
     */
    private @Nullable MergePartner getNthCandidate(int n) {
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
     * Loads the merge candidates into the combo box, initializes the partner editor pane with
     * the text of the first candidate and computes the initial button enablement (Swing
     * {@code loadCandidates}).
     */
    private void loadCandidates() {
        if (candidates.isEmpty()) {
            checkApplicable();
            return;
        }

        for (MergePartner candidate : candidates) {
            cmbCandidates.getItems().add("Node " + candidate.getGoal().node().serialNr());
        }
        cmbCandidates.getSelectionModel().selectFirst();

        checkApplicable();
    }

    /**
     * Renders the sequent of the given goal into the given {@link TextFlow}, with the portion
     * that corresponds to the given position rendered in bold (Swing
     * {@code setHighlightedSequentForArea}, which built {@code <b>} HTML markup around the
     * matched subterm).
     * <p>
     * Deviation: the Swing original's {@code before} slice dropped one character before the
     * match ({@code substring(0, m.start() - 1)}, an HTML-escaping artifact); the port renders
     * the full matched range.
     *
     * @param goal Goal to render.
     * @param pio Position indicating subterm to highlight.
     * @param flow The flow to render the highlighted goal into.
     */
    private static void setHighlightedSequentForArea(Goal goal,
            PosInOccurrence pio, TextFlow flow) {
        Services svcs = goal.proof().getServices();
        String subterm = LogicPrinter.quickPrintTerm((JTerm) pio.subTerm(), svcs);

        // Render subterm to highlight as a regular expression (as in the Swing original).
        subterm = subterm.replaceAll("\\s", "\\\\s");
        subterm = subterm.replaceAll("(\\\\s)+", "\\\\E\\\\s*\\\\Q");
        subterm = "\\Q" + subterm + "\\E";
        if (subterm.endsWith("\\Q\\E")) {
            subterm = subterm.substring(0, subterm.length() - 4);
        }

        // Find a match in the printed sequent
        String sequent = LogicPrinter.quickPrintSequent(goal.sequent(), svcs);
        Pattern p = Pattern.compile(subterm);
        Matcher m = p.matcher(sequent);

        int matchStart = -1;
        int matchEnd = -1;
        if (m.find()) {
            matchStart = m.start();
            matchEnd = m.end();
        }

        Text before = new Text(matchStart >= 0 ? sequent.substring(0, matchStart) : sequent);
        before.setFont(TXT_AREA_FONT);
        flow.getChildren().setAll(before);
        if (matchStart >= 0) {
            Text main = new Text(sequent.substring(matchStart, matchEnd));
            main.setFont(TXT_AREA_FONT_BOLD);
            Text after = new Text(sequent.substring(matchEnd));
            after.setFont(TXT_AREA_FONT);
            flow.getChildren().addAll(main, after);
        }
    }

}
