/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.mergerule.predicateabstraction;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Optional;
import java.util.Scanner;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.RadioButton;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TableCell;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleGroup;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.ConjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.DisjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.SimplePredicateAbstractionLattice;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog to choose abstraction predicates for merges with predicate abstraction.
 * <p>
 * Port of the Swing
 * {@code de.uka.ilkd.key.gui.mergerule.predicateabstraction.AbstractionPredicatesChoiceDialog}
 * (key.ui): the four step tabs (lattice type, placeholder variables, abstraction predicates,
 * manual domain element choices) and the problems pane behave as in the original. Deviations
 * (documented, no javafx.web bundled): the information panel and the problems pane render the
 * original HTML resources as plain text instead of HTML; the {@code ObservableArrayList} helper
 * of the original is replaced by the native JavaFX {@link ObservableList}.
 *
 * @author Dominic Steinhoefel (original Swing dialog)
 */
public final class AbstractionPredicatesChoiceDialogF {

    private static final String AVAILABLE_PROGRAM_VARIABLES_DESCR = "Available Program Variables: ";

    /** The initial size of this dialog. */
    private static final double INITIAL_WIDTH = 850;
    private static final double INITIAL_HEIGHT = 600;

    private static final String DIALOG_TITLE = "Choose abstraction predicates for merge";

    private static final Logger LOGGER =
        LoggerFactory.getLogger(AbstractionPredicatesChoiceDialogF.class);

    private final Stage stage = new Stage();

    @Nullable
    private Goal goal = null;

    private ArrayList<Pair<Sort, Name>> registeredPlaceholders = new ArrayList<>();
    private ArrayList<AbstractionPredicate> registeredPredicates = new ArrayList<>();
    private final ArrayList<AbstractDomainElemChoiceF> abstrPredicateChoices = new ArrayList<>();

    private Class<? extends AbstractPredicateAbstractionLattice> latticeType =
        SimplePredicateAbstractionLattice.class;

    /** Problems for the placeholder variables input (replaces the Swing ObservableArrayList). */
    private final ObservableList<String> placeholdersProblems = FXCollections.observableArrayList();
    /** Problems for the abstraction predicates input. */
    private final ObservableList<String> abstrPredProblems = FXCollections.observableArrayList();

    private final ListView<String> placeholdersList = new ListView<>();
    private final ListView<String> abstrPredsList = new ListView<>();
    private final ListView<String> problemsList = new ListView<>();
    private final TableView<AbstractDomainElemChoiceF> choiceTable =
        new TableView<>(FXCollections.observableArrayList(abstrPredicateChoices));
    private final Services services;
    private boolean cancelled = false;

    /**
     * Constructs a new {@link AbstractionPredicatesChoiceDialogF}. The given goal is used to get
     * information about the proof.
     *
     * @param goal The goal on which the merge rule is applied.
     * @param differingLocVars Location variables the values of which differ in the merge partner
     *        states.
     * @param owner the owner window for the modal dialog (may be null)
     */
    public AbstractionPredicatesChoiceDialogF(Goal goal, List<LocationVariable> differingLocVars,
            @Nullable Window owner) {
        this(goal.proof().getServices(), owner);
        this.goal = goal;
        differingLocVars
                .forEach(v -> abstrPredicateChoices.add(new AbstractDomainElemChoiceF(v,
                    Optional.empty())));
        choiceTable.getItems().setAll(abstrPredicateChoices);
    }

    /**
     * Constructs a new dialog without a goal (test mode, as in the Swing original's no-arg
     * constructor).
     *
     * @param services the services (may be null in test mode)
     * @param owner the owner window for the modal dialog (may be null)
     */
    public AbstractionPredicatesChoiceDialogF(@Nullable Services services,
            @Nullable Window owner) {
        this.services = services;

        stage.setTitle(DIALOG_TITLE);
        stage.setMinWidth(650);
        stage.setMinHeight(450);

        final BorderPane root = new BorderPane();
        root.setTop(createInfoPanel());
        root.setCenter(createCenter());
        root.setBottom(createControlsPanel());

        if (owner != null) {
            stage.initOwner(owner);
        }
        stage.initModality(owner != null ? Modality.WINDOW_MODAL : Modality.APPLICATION_MODAL);
        Scene scene = new Scene(root, INITIAL_WIDTH, INITIAL_HEIGHT);
        ThemeManager.getInstance().style(scene);
        stage.setScene(scene);

        // the Swing original listens on both problem lists and rebuilds the problems pane
        ListChangeListener<String> listener = change -> refreshProblems();
        placeholdersProblems.addListener(listener);
        abstrPredProblems.addListener(listener);
    }

    private VBox createInfoPanel() {
        final Label heading = new Label("Information on Merges with Predicate Abstraction");
        heading.getStyleClass().add("dialog-section-title");

        // the Swing original renders the HTML resource in a JTextPane; without javafx.web we
        // degrade to the plain text content (strip tags)
        String html =
            readFromResourceFile("/de/uka/ilkd/key/gui/help/abstrPredsMergeDialogInfo.html");
        TextArea info = new TextArea(html == null ? "" : stripHtml(html));
        info.setEditable(false);
        info.setWrapText(true);

        VBox box = new VBox(2, heading, info);
        box.setPadding(new Insets(4, 8, 4, 8));
        VBox.setVgrow(info, Priority.ALWAYS);
        return box;
    }

    private SplitPane createCenter() {
        final TabPane stepsTabbedPane = new TabPane();
        stepsTabbedPane.getTabs().addAll(
            new Tab("(1) Lattice Type", createLatticeTypePanel()),
            new Tab("(2) Placeholder Variables", createPlaceholderVariablesPanel()),
            new Tab("(3) Abstraction Predicates", createAbstractionPredicatesPanel()),
            new Tab("(4) Choice of Abstraction Predicates [opt]", createChoiceAbstrPredsPanel()));

        final Label problemsHeading = new Label("Problems");
        problemsHeading.getStyleClass().add("dialog-section-title");
        VBox problemsPane = new VBox(2, problemsHeading, problemsList);
        problemsPane.setPadding(new Insets(4, 8, 4, 8));
        VBox.setVgrow(problemsList, Priority.ALWAYS);

        SplitPane split = new SplitPane(stepsTabbedPane, problemsPane);
        SplitPane.setResizableWithParent(stepsTabbedPane, Boolean.TRUE);
        split.setDividerPositions(0.7);
        return split;
    }

    private VBox createLatticeTypePanel() {
        final ToggleGroup group = new ToggleGroup();
        RadioButton simple = new RadioButton("Simple Predicates Lattice");
        simple.setToggleGroup(group);
        simple.setSelected(true);
        simple.setOnAction(e -> latticeType = SimplePredicateAbstractionLattice.class);
        RadioButton conj = new RadioButton("Conjunctive Predicates Lattice");
        conj.setToggleGroup(group);
        conj.setOnAction(e -> latticeType = ConjunctivePredicateAbstractionLattice.class);
        RadioButton disj = new RadioButton("Disjunctive Predicates Lattice");
        disj.setToggleGroup(group);
        disj.setOnAction(e -> latticeType = DisjunctivePredicateAbstractionLattice.class);

        VBox box = new VBox(4, simple, conj, disj);
        box.setPadding(new Insets(8));
        return box;
    }

    private BorderPane createPlaceholderVariablesPanel() {
        final TextField input = new TextField();
        input.setPromptText("Enter a new placeholder variable (e.g., \"int _ph1\")");

        input.setOnAction(e -> {
            final String currInput = input.getText().strip();
            if (currInput.isEmpty()) {
                return;
            }
            try {
                final Pair<Sort, Name> parsed = parsePlaceholder(currInput);
                placeholdersProblems.clear();
                placeholdersList.getItems().add(currInput);
                input.setText("");
                registeredPlaceholders.add(parsed);
                if (goal != null) {
                    final Namespace<IProgramVariable> pvs =
                        goal.proof().getServices().getNamespaces().programVariables();
                    pvs.add(new LocationVariable(
                        new ProgramElementName(parsed.second.toString()), parsed.first));
                }
            } catch (Exception ex) {
                placeholdersProblems.clear();
                placeholdersProblems.add(ex.getMessage());
                LOGGER.error("Exception!", ex);
            }
        });

        // Swing: DEL on a selected list entry removes the placeholder (and unbinds it)
        placeholdersList.setOnKeyPressed(e -> {
            int selectedIndex = placeholdersList.getSelectionModel().getSelectedIndex();
            if (e.getCode() == KeyCode.DELETE && !placeholdersList.getItems().isEmpty()
                    && selectedIndex >= 0) {
                String removedInput = placeholdersList.getItems().remove(selectedIndex);
                if (registeredPlaceholders.size() > selectedIndex && goal != null) {
                    final Pair<Sort, Name> removedPlaceholder =
                        registeredPlaceholders.remove(selectedIndex);
                    final Namespace<IProgramVariable> pvs =
                        goal.proof().getServices().getNamespaces().programVariables();
                    pvs.remove(removedPlaceholder.second);
                }
                LOGGER.debug("Removed placeholder {}", removedInput);
            }
        });

        // keep the input listener in sync with the Swing original: live validation on typing
        input.textProperty().addListener((obs, oldV, currInput) -> {
            if (currInput.isEmpty()) {
                placeholdersProblems.clear();
                return;
            }
            try {
                parsePlaceholder(currInput.strip());
                placeholdersProblems.clear();
            } catch (Exception ex) {
                placeholdersProblems.clear();
                placeholdersProblems.add(ex.getMessage());
            }
        });

        BorderPane pane = new BorderPane(placeholdersList, input, null, null, null);
        BorderPane.setMargin(input, new Insets(4));
        VBox.setVgrow(placeholdersList, Priority.ALWAYS);
        return pane;
    }

    private BorderPane createAbstractionPredicatesPanel() {
        final TextField input = new TextField();
        input.setPromptText("Enter a new predicate (e.g., \"_ph1 > 0\").");

        BorderPane pane = new BorderPane();
        pane.setTop(input);
        BorderPane.setMargin(input, new Insets(4));

        VBox center = new VBox(4, abstrPredsList);
        VBox.setVgrow(abstrPredsList, Priority.ALWAYS);
        pane.setCenter(center);

        // Goal will only be null in test run
        if (goal != null) {
            String progVarsStr = goal.node().getLocalProgVars().toString().replace(",", ", ");
            progVarsStr = progVarsStr.substring(1, progVarsStr.length() - 1);
            pane.setBottom(new Label(AVAILABLE_PROGRAM_VARIABLES_DESCR + progVarsStr));
        }

        input.textProperty().addListener((obs, oldV, currInput) -> {
            if (currInput.isEmpty()) {
                abstrPredProblems.clear();
                return;
            }
            try {
                parsePredicate(currInput.strip());
                abstrPredProblems.clear();
                if (registeredPredicates.contains(parsePredicate(currInput.strip()))) {
                    abstrPredProblems.add("Predicate is already registered");
                }
            } catch (Exception ex) {
                abstrPredProblems.clear();
                abstrPredProblems.add(ex.getMessage());
            }
        });

        input.setOnAction(e -> {
            final String currInput = input.getText().strip();
            if (currInput.isEmpty() || !abstrPredProblems.isEmpty()) {
                return;
            }
            try {
                AbstractionPredicate parsed = parsePredicate(currInput);
                abstrPredsList.getItems().add(currInput);
                input.setText("");
                registeredPredicates.add(parsed);
            } catch (Exception ex) {
                abstrPredProblems.clear();
                abstrPredProblems.add(ex.getMessage());
                LOGGER.error("Exception!", ex);
            }
        });

        abstrPredsList.setOnKeyPressed(e -> {
            int selectedIndex = abstrPredsList.getSelectionModel().getSelectedIndex();
            if (e.getCode() == KeyCode.DELETE && !abstrPredsList.getItems().isEmpty()
                    && selectedIndex >= 0) {
                abstrPredsList.getItems().remove(selectedIndex);
                if (registeredPredicates.size() > selectedIndex) {
                    registeredPredicates.remove(selectedIndex);
                }
            }
        });

        return pane;
    }

    private BorderPane createChoiceAbstrPredsPanel() {
        TableColumn<AbstractDomainElemChoiceF, String> progVarCol =
            new TableColumn<>("Program Variable");
        progVarCol.setCellValueFactory(
            c -> new javafx.beans.property.SimpleStringProperty(
                c.getValue().getProgVar().sort() + " " + c.getValue().getProgVar().name()));
        progVarCol.setPrefWidth(180);

        TableColumn<AbstractDomainElemChoiceF, AbstractDomainElemChoiceF> domElemCol =
            new TableColumn<>("Domain Element");
        domElemCol.setCellValueFactory(c -> new javafx.beans.property.SimpleObjectProperty<>(
            c.getValue()));
        domElemCol.setCellFactory(col -> new DomainElemChoiceCell());
        domElemCol.setPrefWidth(380);

        choiceTable.getColumns().setAll(List.of(progVarCol, domElemCol));
        choiceTable.setColumnResizePolicy(TableView.CONSTRAINED_RESIZE_POLICY_FLEX_LAST_COLUMN);
        choiceTable.setPlaceholder(new Label("No differing program variables."));

        return new BorderPane(choiceTable);
    }

    /**
     * A table cell with a {@link ComboBox} of the domain elements of the row variable's sort
     * (Swing: {@code DomElemChoiceTable.getCellEditor}/{@code getCellRenderer} with the
     * {@code Optional<AbstractPredicateAbstractionDomainElement>} item model).
     */
    private final class DomainElemChoiceCell
            extends TableCell<AbstractDomainElemChoiceF, AbstractDomainElemChoiceF> {
        private final ComboBox<Optional<AbstractPredicateAbstractionDomainElement>> items =
            new ComboBox<>();

        @Override
        protected void updateItem(AbstractDomainElemChoiceF item, boolean empty) {
            super.updateItem(item, empty);
            if (empty || item == null) {
                setText(null);
                setGraphic(null);
                return;
            }
            items.getItems().clear();
            items.getItems().add(Optional.empty());
            if (services != null && goal != null) {
                final Sort s = item.getProgVar().sort();
                final AbstractDomainLattice lattice = new MergeWithPredicateAbstraction(
                    registeredPredicates, latticeType, new LinkedHashMap<>())
                        .getAbstractDomainForSort(s, services);
                if (lattice != null) {
                    for (AbstractDomainElement elem : lattice) {
                        items.getItems()
                                .add(Optional.of(
                                    (AbstractPredicateAbstractionDomainElement) elem));
                    }
                }
            }
            items.getSelectionModel().select(item.getAbstrDomElem());
            items.setCellFactory(view -> new ListCell<>() {
                @Override
                protected void updateItem(Optional<AbstractPredicateAbstractionDomainElement> it,
                        boolean empty) {
                    super.updateItem(it, empty);
                    setText(empty || it == null ? null : abstrPredToStringRepr(it));
                }
            });
            items.setButtonCell(new ListCell<>() {
                @Override
                protected void updateItem(Optional<AbstractPredicateAbstractionDomainElement> it,
                        boolean empty) {
                    super.updateItem(it, empty);
                    setText(empty || it == null ? null : abstrPredToStringRepr(it));
                }
            });
            items.valueProperty().addListener((obs, oldV, newV) -> item.setAbstrDomElem(newV));
            setGraphic(items);
            setText(null);
        }
    }

    private HBox createControlsPanel() {
        final Button cancelButton = new Button("Cancel");
        cancelButton.setCancelButton(true);
        cancelButton.setOnAction(e -> {
            cancelled = true;
            stage.close();
        });
        final Button okButton = new Button("OK");
        okButton.setDefaultButton(true);
        okButton.setOnAction(e -> stage.close());

        HBox box = new HBox(8, cancelButton, okButton);
        box.setAlignment(Pos.CENTER);
        box.setPadding(new Insets(8));
        return box;
    }

    private void refreshProblems() {
        final ObservableList<String> data = problemsList.getItems();
        data.clear();
        if (!placeholdersProblems.isEmpty()) {
            for (String problem : placeholdersProblems) {
                data.add("Placeholder Variables: " + problem);
            }
        }
        if (!abstrPredProblems.isEmpty()) {
            for (String problem : abstrPredProblems) {
                data.add("Abstraction Predicates: " + problem);
            }
        }
    }

    /**
     * Parses a placeholder using {@link MergeRuleUtils#parsePlaceholder(String, Services)}.
     *
     * @param input The input to parse.
     * @return The parsed placeholder (sort and name).
     */
    private Pair<Sort, Name> parsePlaceholder(String input) {
        return MergeRuleUtils.parsePlaceholder(input, goal.proof().getServices());
    }

    /**
     * Parses an abstraction predicate using
     * {@link MergeRuleUtils#parsePredicate(String, ArrayList, NamespaceSet, Services)}.
     *
     * @param input The input to parse.
     * @return The parsed abstraction predicate.
     * @throws ParserException If there is a mistake in the input.
     */
    private AbstractionPredicate parsePredicate(String input) throws ParserException {
        return MergeRuleUtils.parsePredicate(input, registeredPlaceholders,
            goal.getLocalNamespaces(), goal.proof().getServices());
    }

    /**
     * A String representation of an abstraction domain element, that is a "pair" expression of
     * the placeholder variable and the predicate term of the form "(PROGVAR,PREDTERM)"
     * (Swing {@code abstrPredToStringRepr}).
     *
     * @param domElem The abstraction predicate to convert into a String representation.
     * @return A String representation of the given abstraction domain element.
     */
    private String abstrPredToStringRepr(
            Optional<AbstractPredicateAbstractionDomainElement> domElem) {
        if (domElem == null) {
            return "";
        }

        if (!domElem.isPresent()) {
            return "None.";
        }

        final AbstractPredicateAbstractionDomainElement predElem = domElem.get();

        if (predElem.getPredicates().isEmpty()) {
            return predElem.toString();
        }

        final StringBuilder sb = new StringBuilder();

        final Iterator<AbstractionPredicate> it = predElem.getPredicates().iterator();

        while (it.hasNext()) {
            sb.append(abstrPredToString(it.next()));

            if (it.hasNext()) {
                sb.append(predElem.getPredicateNameCombinationString());
            }
        }

        return sb.toString();
    }

    /**
     * Returns a String representation of an abstraction predicate
     * (Swing {@code abstrPredToString}; the Swing original fetches the services from the
     * global MainWindow mediator, the port receives them in the constructor).
     *
     * @param pred Predicate to compute a String representation for.
     * @return A String representation of the given abstraction predicate.
     */
    private String abstrPredToString(AbstractionPredicate pred) {
        if (services == null) {
            return pred.toString();
        }
        final Pair<LocationVariable, de.uka.ilkd.key.logic.JTerm> predFormWithPh =
            pred.getPredicateFormWithPlaceholder();

        return "(" + predFormWithPh.first + ","
            + OutputStreamProofSaver.printAnything(predFormWithPh.second, services) + ")";
    }

    /**
     * Shows the dialog modally and blocks until it is closed.
     */
    public void show() {
        stage.showAndWait();
    }

    // joinmerge: test support for the key.fx.verify.joinmerge self test — non-blocking show and
    // programmatic cancel with the same semantics as the cancel button; the production path
    // uses show().

    /** Shows the dialog without blocking (self-test support; parity with {@link #show()}). */
    public void showNonBlocking() {
        stage.show();
    }

    /** Cancels the dialog (self-test support; parity with the cancel button). */
    public void requestCancel() {
        cancelled = true;
        stage.close();
    }

    /** Exposes the dialog stage for tests. */
    public Stage getStageForVerification() {
        return stage;
    }

    /**
     * @return The abstraction predicates set by the user. Is null iff the user pressed cancel.
     */
    private @Nullable ArrayList<AbstractionPredicate> getRegisteredPredicates() {
        return cancelled ? null : registeredPredicates;
    }

    /**
     * @return The chosen lattice type (class object for class that is an instance of
     *         {@link AbstractPredicateAbstractionLattice}).
     */
    private Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType;
    }

    /**
     * @return The resulting input supplied by the user.
     */
    public Result getResult() {
        return new Result(getRegisteredPredicates(), getLatticeType(), abstrPredicateChoices);
    }

    // ///////////////////////////// //
    // /////// STATIC METHODS ////// //
    // ///////////////////////////// //

    private static @Nullable URL getURLForResourceFile(String filename) {
        URL url = AbstractionPredicatesChoiceDialogF.class.getResource(filename);
        if (url == null) {
            LOGGER.error("No resource {} found", filename);
        }
        return url;
    }

    private static @Nullable String readFromResourceFile(String filename) {
        URL url = getURLForResourceFile(filename);
        if (url == null) {
            return null;
        }
        try (final InputStream is = url.openStream();
                final Scanner s = new Scanner(is, StandardCharsets.UTF_8)) {
            return s.useDelimiter("\\A").next();
        } catch (IOException e) {
            return null;
        }
    }

    /**
     * Crude HTML to text degradation for the info/help resources (the Swing original rendered
     * them with the JTextPane HTML engine; javafx.web is deliberately not bundled in
     * key.ui.fx).
     *
     * @param html the html resource content
     * @return the text content without tags and entities
     */
    static String stripHtml(String html) {
        String text = html.replaceAll("(?is)<(script|style).*?</\\1>", "");
        text = text.replaceAll("(?s)<[^>]*>", " ");
        text = text.replace("&nbsp;", " ").replace("&amp;", "&").replace("&lt;", "<")
                .replace("&gt;", ">").replace("&quot;", "\"");
        return text.replaceAll("\\n\\s*\\n+", "\n\n").strip();
    }

    /**
     * Encapsulates the results supplied by the user (Swing inner {@code Result} class,
     * unchanged).
     */
    public static class Result {
        private final @Nullable ArrayList<AbstractionPredicate> registeredPredicates;
        private final Class<? extends AbstractPredicateAbstractionLattice> latticeType;
        private final LinkedHashMap<ProgramVariable, AbstractDomainElement> abstractDomElemUserChoices =
            new LinkedHashMap<>();

        public Result(@Nullable ArrayList<AbstractionPredicate> registeredPredicates,
                Class<? extends AbstractPredicateAbstractionLattice> latticeType,
                List<AbstractDomainElemChoiceF> userChoices) {
            this.registeredPredicates = registeredPredicates;
            this.latticeType = latticeType;

            userChoices.forEach(choice -> {
                if (choice.isChoiceMade()) {
                    abstractDomElemUserChoices.put(choice.getProgVar(),
                        choice.getAbstrDomElem().get());
                }
            });
        }

        /**
         * @return The abstraction predicates set by the user. Is null iff the user pressed
         *         cancel.
         */
        public @Nullable ArrayList<AbstractionPredicate> getRegisteredPredicates() {
            return registeredPredicates;
        }

        /**
         * @return The chosen lattice type (class object for class that is an instance of
         *         {@link AbstractPredicateAbstractionLattice}).
         */
        public Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
            return latticeType;
        }

        /**
         * @return Manually chosen lattice elements for program variables.
         */
        public LinkedHashMap<ProgramVariable, AbstractDomainElement> getAbstractDomElemUserChoices() {
            return abstractDomElemUserChoices;
        }
    }
}
