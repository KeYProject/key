// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2016 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.joinrule.predicateabstraction;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Optional;
import java.util.stream.Collectors;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ListChangeListener.Change;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.Accordion;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableColumn.CellDataFeatures;
import javafx.scene.control.TableView;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.AnchorPane;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.util.StringConverter;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.ConjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.DisjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.SimplePredicateAbstractionLattice;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstraction;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.Pair;

/**
 * The JavaFX controller for the predicates choice dialog GUI.
 *
 * @author Dominic Scheurer
 */
public class AbstractionPredicatesChoiceDialogController {
    // ///////////////////////////// //
    // /////// FXML BINDINGS /////// //
    // ///////////////////////////// //
    @FXML
    private Accordion accMain;

    @FXML
    private TextField txtPlaceholders;

    @FXML
    private ListView<String> lvPlaceholders;

    @FXML
    private TextField txtPredicates;

    @FXML
    private ListView<String> lvPredicates;

    @FXML
    private Label lblAvailableProgVars;

    @FXML
    private WebView wvProblems;

    @FXML
    private WebView wvInfo;

    @FXML
    private TitledPane tpLatticeElemChoice;

    @FXML
    private TableView<AbstractDomainElemChoice> tvLatticeElemChoice;

    @FXML
    private AnchorPane mainPane;

    // ///////////////////////////// //
    // /////// PRIVATE FIELDS ////// //
    // ///////////////////////////// //

    // ///////////////////////////// //
    // ////////// SETTERS ////////// //
    // ///////////////////////////// //

    /**
     * Sets the text for the "available program variables" label.
     * 
     * @param progVarsStr
     *            A string representation of the available program variables.
     */
    public void setAvailableProgVarsInfoTxt(String progVarsStr) {
        lblAvailableProgVars.setText("Available Program Variables: "
                + progVarsStr);
    }

    // ///////////////////////////// //
    // //////// PROPERTIES ///////// //
    // ///////////////////////////// //

    // Observable lists for problems. May be changed from an outside
    // controller and are watched by this class.
    final ObservableList<String> placeholdersProblemsListData = FXCollections
            .observableArrayList();

    final ObservableList<String> predicateProblemsListData = FXCollections
            .observableArrayList();

    // Observable list encapsulating already accepted placeholders.
    private final ObservableList<String> placeholderList = FXCollections
            .observableArrayList();

    // Observable list encapsulating already accepted abstraction predicates.
    private final ObservableList<String> predicatesList = FXCollections
            .observableArrayList();

    // Observable list encapsulating the abstraction predicate choices
    // by the user. May be changed from an outside controller.
    final ObservableList<AbstractDomainElemChoice> abstrPredicateChoices =
            FXCollections.observableArrayList();

    // Observable list encapsulating the available parsed abstraction predicates
    // for the manual choice of predicates by the user. May be changed from an
    // outside controller.
    final ObservableList<AbstractionPredicate> availableAbstractionPreds =
            FXCollections.observableArrayList();

    // Property for the chosen lattice type
    private ObjectProperty<Class<? extends AbstractPredicateAbstractionLattice>> latticeType =
            new SimpleObjectProperty<Class<? extends AbstractPredicateAbstractionLattice>>(
                    SimplePredicateAbstractionLattice.class);

    public final Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType.get();
    }

    public final void setLatticeType(
            Class<? extends AbstractPredicateAbstractionLattice> latticeType) {
        this.latticeType.set(latticeType);
    }

    public ObjectProperty<Class<? extends AbstractPredicateAbstractionLattice>> latticeTypeProperty() {
        return latticeType;
    }

    // Properties for pressing OK and close
    private BooleanProperty okPressed = new SimpleBooleanProperty();

    public final boolean getOkPressed() {
        return okPressed.get();
    }

    public final void setOkPressed(boolean okPressed) {
        this.okPressed.set(okPressed);
    }

    public BooleanProperty okPressedProperty() {
        return okPressed;
    }

    private BooleanProperty cancelPressed = new SimpleBooleanProperty();

    public final boolean getCancelPressedPressed() {
        return cancelPressed.get();
    }

    public final void setCancelPressed(boolean cancelPressed) {
        this.cancelPressed.set(cancelPressed);
    }

    public BooleanProperty cancelPressedProperty() {
        return cancelPressed;
    }

    // Property encapsulating the currently typed placeholder
    private SimpleStringProperty currentPlaceholder =
            new SimpleStringProperty();

    public final String getCurrentPlaceholder() {
        return currentPlaceholder.get();
    }

    public final void setCurrentPlaceholder(String currentPlaceholder) {
        this.currentPlaceholder.set(currentPlaceholder);
    }

    public SimpleStringProperty currentPlaceholderProperty() {
        return currentPlaceholder;
    }

    // Property encapsulating the currently typed predicate
    private SimpleStringProperty currentPredicate = new SimpleStringProperty();

    public final String getCurrentPredicate() {
        return currentPlaceholder.get();
    }

    public final void setCurrentPredicate(String currentPredicate) {
        this.currentPredicate.set(currentPredicate);
    }

    public SimpleStringProperty currentPredicateProperty() {
        return currentPredicate;
    }

    // ///////////////////////////// //
    // /////// FXML HANDLERS /////// //
    // ///////////////////////////// //

    @FXML
    private void initialize() {
        accMain.setExpandedPane(accMain.getPanes().get(0));

        final String resourcePath = "/de/uka/ilkd/key/gui/";
        final URL bootstrapCssResource =
                getURLForResourceFile(AbstractionPredicatesChoiceDialog.class,
                        resourcePath + "css/bootstrap/bootstrap.min.css");
        final URL bootstrapThemeCssResource =
                getURLForResourceFile(AbstractionPredicatesChoiceDialog.class,
                        resourcePath + "css/bootstrap/bootstrap-theme.min.css");
        final URL infoTextResource =
                getURLForResourceFile(AbstractionPredicatesChoiceDialog.class,
                        resourcePath + "help/abstrPredsJoinDialogInfo.html");
        
        assert bootstrapCssResource != null
                && bootstrapThemeCssResource != null
                && infoTextResource != null : "Could not find css/html resources for the abstraction predicates choice dialog.";

        mainPane.prefWidthProperty().bind(wvInfo.prefWidthProperty());

        {
            final WebEngine webEngine = wvInfo.getEngine();
            final StringBuilder sb = new StringBuilder();
            sb.append("<html><head>");

            sb.append("<link href=\"");
            sb.append(bootstrapCssResource);
            sb.append("\" type=\"text/css\" rel=\"stylesheet\">");

            sb.append("<link href=\"");
            sb.append(bootstrapThemeCssResource);
            sb.append("\" type=\"text/css\" rel=\"stylesheet\">");

            sb.append("</head><body>");
            try {
               InputStream is = infoTextResource.openStream();
               sb.append(new BufferedReader(new InputStreamReader(is)).lines().collect(Collectors.joining("\n")));
               is.close();
            }
            catch (IOException e) {}
            sb.append("</body></html>");
            webEngine.loadContent(sb.toString());
        }

        ListChangeListener<String> changeListener =
                (Change<? extends String> event) -> {
                    final WebEngine webEngine = wvProblems.getEngine();

                    final StringBuilder sb = new StringBuilder();
                    sb.append("<html><head>");

                    sb.append("<link href=\"");
                    sb.append(bootstrapCssResource);
                    sb.append("\" type=\"text/css\" rel=\"stylesheet\">");

                    sb.append("<link href=\"");
                    sb.append(bootstrapThemeCssResource);
                    sb.append("\" type=\"text/css\" rel=\"stylesheet\">");

                    sb.append("</head><body style=\"padding: 0 5px 0 5px;\">");

                    if (!placeholdersProblemsListData.isEmpty()) {
                        sb.append("<h3>Placeholder Variables</h3>");
                        sb.append("<table class=\"table table-striped\">");
                        for (String problem : placeholdersProblemsListData) {
                            sb.append("<tr><td>").append(problem)
                                    .append("</td></tr>");
                        }
                        sb.append("</table>");
                    }

                    if (!predicateProblemsListData.isEmpty()) {
                        sb.append("<h3>Abstraction Predicates</h3>");
                        sb.append("<table class=\"table table-striped\">");
                        for (String problem : predicateProblemsListData) {
                            sb.append("<tr><td>").append(problem)
                                    .append("</td></tr>");
                        }
                        sb.append("</table>");
                    }

                    sb.append("</body></html>");

                    webEngine.loadContent(sb.toString());
                };

        placeholdersProblemsListData.addListener(changeListener);
        predicateProblemsListData.addListener(changeListener);

        tpLatticeElemChoice.expandedProperty().addListener(
                (ObservableValue<? extends Boolean> e, Boolean oldValue,
                        Boolean newValue) -> {
                    if (newValue && !oldValue) {
                        populateAbstrPredChoiceTable();
                    }
                });
    }

    @FXML
    private void handleCancel() {
        setCancelPressed(true);
    }

    @FXML
    private void handleOK() {
        setOkPressed(true);
    }

    @FXML
    private void handleKeyReleasedInInputTextField(KeyEvent e) {
        final TextField src = (TextField) e.getSource();
        final ListView<String> lv;
        final boolean isValid;

        if (src == txtPlaceholders) {
            setCurrentPlaceholder(src.getText());

            lv = lvPlaceholders;
            isValid = placeholdersProblemsListData.isEmpty();
        }
        else {
            setCurrentPredicate(src.getText());

            lv = lvPredicates;
            isValid = predicateProblemsListData.isEmpty();
        }

        if (!isValid) {
            src.setStyle("-fx-control-inner-background: #FF0000");
        }
        else {
            src.setStyle("-fx-control-inner-background: #FFFFFF");
        }

        if (isValid && e.getCode().equals(KeyCode.ENTER)
                && !src.getText().isEmpty()) {
            lv.getItems().add(src.getText());

            if (lv == lvPlaceholders) {
                placeholderList.add(src.getText());
            }
            else if (lv == lvPredicates) {
                predicatesList.add(src.getText());
            }
            else {
                assert false : "There should not be another source than the two known list views.";
            }

            src.setText("");
        }
    }

    @FXML
    private void handleKeyReleasedInListview(KeyEvent e) {
        if (e.getCode().equals(KeyCode.DELETE)) {

            @SuppressWarnings("unchecked")
            ListView<String> lvSource = (ListView<String>) e.getSource();

            if (lvSource == lvPlaceholders
                    && lvPredicates.getItems().size() > 0) {
                Alert delConfirmAlert = new Alert(AlertType.CONFIRMATION);
                delConfirmAlert.setTitle("Deleting a placeholder variable");
                delConfirmAlert
                        .setHeaderText("You are about to delete a placeholder variable");
                delConfirmAlert
                        .setContentText("Deleting a placeholder that is used in an "
                                + "abstraction predicate will cause problems whenever "
                                + "the predicate is used. Please make sure that you "
                                + "really do not need the placeholder.\n\n"
                                + "Do you want to continue?");
                delConfirmAlert.setResizable(true);
                delConfirmAlert.getDialogPane().setPrefSize(480, 320);

                Optional<ButtonType> result = delConfirmAlert.showAndWait();
                if (result.get() != ButtonType.OK) {
                    return;
                }
            }

            int idx = lvSource.getSelectionModel().getSelectedIndex();
            lvSource.getItems().remove(idx);

            if (lvSource == lvPlaceholders) {
                placeholderList.remove(idx);
            }
            else if (lvSource == lvPredicates) {
                predicatesList.remove(idx);
            }
            else {
                assert false : "There should not be another source than the two known list views.";
            }
        }
    }

    @FXML
    private void simplePredicatesLatticeChosen(ActionEvent e) {
        setLatticeType(SimplePredicateAbstractionLattice.class);
    }

    @FXML
    private void conjunctivePredicatesLatticeChosen(ActionEvent e) {
        setLatticeType(ConjunctivePredicateAbstractionLattice.class);
    }

    @FXML
    private void disjunctivePredicatesLatticeChosen(ActionEvent e) {
        setLatticeType(DisjunctivePredicateAbstractionLattice.class);
    }

    // ///////////////////////////// //
    // /// OTHER PRIVATE METHODS /// //
    // ///////////////////////////// //

    private void populateAbstrPredChoiceTable() {
        final TableColumn<AbstractDomainElemChoice, ProgramVariable> progVarCol =
                new TableColumn<AbstractDomainElemChoice, ProgramVariable>(
                        "Program Variable");

        progVarCol.setPrefWidth(180);
        progVarCol.setEditable(false);
        progVarCol
                .setCellValueFactory(choice -> choice.getValue().getProgVar());

        progVarCol
                .setCellFactory(p -> new TextFieldTableCell<AbstractDomainElemChoice, ProgramVariable>(
                        new StringConverter<ProgramVariable>() {
                            @Override
                            public String toString(ProgramVariable pv) {
                                return pv.sort() + " " + pv.name().toString();
                            }

                            @Override
                            public ProgramVariable fromString(String string) {
                                return null;
                            }
                        }));

        final TableColumn<AbstractDomainElemChoice, Optional<AbstractPredicateAbstractionDomainElement>> abstrPredCol =
                new TableColumn<AbstractDomainElemChoice, Optional<AbstractPredicateAbstractionDomainElement>>(
                        "Domain Element");

        abstrPredCol.prefWidthProperty().bind(
                tvLatticeElemChoice.widthProperty().subtract(
                        progVarCol.widthProperty().add(2)));
        abstrPredCol.setEditable(true);

        abstrPredCol
                .setCellValueFactory((
                        CellDataFeatures<AbstractDomainElemChoice, Optional<AbstractPredicateAbstractionDomainElement>> choice) -> choice
                        .getValue().getAbstrDomElem());

        abstrPredCol.setCellFactory(p -> new CustomComboBoxTableCell());

        tvLatticeElemChoice.getColumns().clear();

        tvLatticeElemChoice.getColumns().add(progVarCol);
        tvLatticeElemChoice.getColumns().add(abstrPredCol);

        tvLatticeElemChoice.setItems(abstrPredicateChoices);
        tvLatticeElemChoice.setPlaceholder(new Label("No content available."));

        abstrPredicateChoices.addListener((
                Change<? extends AbstractDomainElemChoice> event) -> {
            tvLatticeElemChoice.setItems(abstrPredicateChoices);
        });
    }

    /**
     * A String representation of an abstraction predicate, that is a "pair"
     * expression of the placeholder variable and the predicate term of the form
     * "(PROGVAR,PREDTERM)".
     * 
     * @param domElem
     *            The abstraction predicate to convert into a String
     *            representation.
     * @return A String representation of the given abstraction predicate.
     */
    private String abstrPredToStringRepr(
            Optional<AbstractPredicateAbstractionDomainElement> domElem) {
        if (domElem == null) {
            return "";
        }

        if (!domElem.isPresent()) {
            return "None.";
        }

        final AbstractPredicateAbstractionDomainElement predElem =
                (AbstractPredicateAbstractionDomainElement) domElem.get();

        if (predElem.getPredicates().size() < 1) {
            return predElem.toString();
        }

        final StringBuilder sb = new StringBuilder();

        final Iterator<AbstractionPredicate> it =
                predElem.getPredicates().iterator();

        while (it.hasNext()) {
            sb.append(abstrPredToString(it.next()));

            if (it.hasNext()) {
                sb.append(predElem.getPredicateNameCombinationString());
            }
        }

        return sb.toString();
    }

    /**
     * Returns a String representation of an abstraction predicate.
     * 
     * @param pred
     *            Predicate to compute a String representation for.
     * @return A String representation of an abstraction predicate.
     */
    private String abstrPredToString(AbstractionPredicate pred) {
        final Services services =
                MainWindow.getInstance().getMediator().getServices();
        final Pair<LocationVariable, Term> predFormWithPh =
                pred.getPredicateFormWithPlaceholder();

        return "("
                + predFormWithPh.first.toString()
                + ","
                + OutputStreamProofSaver.printAnything(predFormWithPh.second,
                        services) + ")";
    }

    // ///////////////////////////// //
    // /// LISTENER REGISTRATION /// //
    // ///////////////////////////// //

    public void registerPlaceholderListListener(
            ListChangeListener<String> listener) {
        placeholderList.addListener(listener);
    }

    public void registerPredicatesListListener(
            ListChangeListener<String> listener) {
        predicatesList.addListener(listener);
    }

    // ///////////////////////////// //
    // /////// STATIC METHODS ////// //
    // ///////////////////////////// //

    public static URL getURLForResourceFile(Class<?> cl, String filename) {
        URL url = cl.getResource(filename);
        Debug.out("Load Resource:" + filename + " of class " + cl);
        if (url == null && cl.getSuperclass() != null) {
            return getURLForResourceFile(cl.getSuperclass(), filename);
        }
        else if (url == null && cl.getSuperclass() == null) {
            // error message Resource not found
            System.out.println("No resource " + filename + " found");
            return null;
        }
        else {
            Debug.out("Done.");
            return url;
        }
    }

    // ///////////////////////////// //
    // /////// INNER CLASSES /////// //
    // ///////////////////////////// //

    /**
     * A table cell displaying a combo box for available abstract domain
     * elements.
     *
     * @author Dominic Scheurer
     */
    class CustomComboBoxTableCell
            extends
            ComboBoxTableCell<AbstractDomainElemChoice, Optional<AbstractPredicateAbstractionDomainElement>> {
        public CustomComboBoxTableCell() {
            super();

            converterProperty()
                    .set(new StringConverter<Optional<AbstractPredicateAbstractionDomainElement>>() {
                        @Override
                        public String toString(
                                Optional<AbstractPredicateAbstractionDomainElement> object) {
                            return abstrPredToStringRepr(object);
                        }

                        @Override
                        public Optional<AbstractPredicateAbstractionDomainElement> fromString(
                                String string) {
                            for (Optional<AbstractPredicateAbstractionDomainElement> pred : getItems()) {
                                if (toString(pred).equals(string)) {
                                    return pred;
                                }
                            }

                            return null;
                        }
                    });
        }

        @Override
        public ObservableList<Optional<AbstractPredicateAbstractionDomainElement>> getItems() {
            // Obtain the right abstract domain for the type of the
            // current program variable

            final Sort s =
                    getTableView().getItems().get(getIndex()).getProgVar()
                            .get().sort();

            final AbstractDomainLattice lattice =
                    new JoinWithPredicateAbstraction(
                            availableAbstractionPreds,
                            latticeType.get(),
                            new LinkedHashMap<ProgramVariable, AbstractDomainElement>())
                            .getAbstractDomainForSort(s, MainWindow
                                    .getInstance().getMediator().getServices());

            // Set all options, including a default one.

            final ObservableList<Optional<AbstractPredicateAbstractionDomainElement>> result =
                    FXCollections.observableArrayList();
            result.add(Optional.empty());

            if (lattice == null) {
                // No predicates have been set for this sort
                return result;
            }

            final Iterator<AbstractDomainElement> it = lattice.iterator();
            while (it.hasNext()) {
                result.add(Optional
                        .of((AbstractPredicateAbstractionDomainElement) it
                                .next()));
            }

            return result;
        }
    }
}
