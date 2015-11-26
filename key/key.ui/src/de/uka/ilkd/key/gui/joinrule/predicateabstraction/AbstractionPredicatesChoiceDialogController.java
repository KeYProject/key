// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.joinrule.predicateabstraction;

import java.io.IOException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Optional;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
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
import javafx.scene.control.ListView;
import javafx.scene.control.TextField;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.AnchorPane;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.ConjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.DisjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.SimplePredicateAbstractionLattice;
import de.uka.ilkd.key.util.Debug;

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
    private WebView wvProblems;

    @FXML
    private WebView wvInfo;

    @FXML
    private AnchorPane mainPane;

    // ///////////////////////////// //
    // //////// PROPERTIES ///////// //
    // ///////////////////////////// //

    // Observable lists for problems. May be changed from an outside
    // controller and are watched by this class.
    ObservableList<String> placeholdersProblemsListData = FXCollections
            .observableArrayList();

    ObservableList<String> predicateProblemsListData = FXCollections
            .observableArrayList();

    // Observable list encapsulating already accepted placeholders.
    private ObservableList<String> placeholderList = FXCollections
            .observableArrayList();

    // Observable list encapsulating already accepted abstraction predicates.
    private ObservableList<String> predicatesList = FXCollections
            .observableArrayList();

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
                        resourcePath
                                + "help/abstrPredsJoinDialogInfo.html");

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
                sb.append(new String(Files.readAllBytes(Paths
                        .get(infoTextResource.getFile()))));
            }
            catch (IOException e) {
            }
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
}
