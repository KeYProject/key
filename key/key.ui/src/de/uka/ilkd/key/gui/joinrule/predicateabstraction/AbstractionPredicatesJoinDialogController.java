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

import java.net.URL;

import javafx.beans.property.SimpleStringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ListChangeListener.Change;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.Accordion;
import javafx.scene.control.ListView;
import javafx.scene.control.TextField;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import de.uka.ilkd.key.util.Debug;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class AbstractionPredicatesJoinDialogController {
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
    }

    @FXML
    private void handleOK() {
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
