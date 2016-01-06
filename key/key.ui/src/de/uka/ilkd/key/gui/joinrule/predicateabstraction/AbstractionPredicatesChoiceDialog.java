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

import java.awt.Dimension;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;

import javafx.application.Platform;
import javafx.beans.value.ObservableValue;
import javafx.collections.ListChangeListener.Change;
import javafx.embed.swing.JFXPanel;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.layout.AnchorPane;

import javax.swing.JDialog;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.SimplePredicateAbstractionLattice;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * A dialog for choosing abstraction predicates for joins with predicate
 * abstraction.
 *
 * @author Dominic Scheurer
 */
public class AbstractionPredicatesChoiceDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    private final static MainWindow MAIN_WINDOW_INSTANCE = MainWindow
            .getInstance();

    /** The initial size of this dialog. */
    private static final Dimension INITIAL_SIZE = new Dimension(850, 600);

    private static final String DIALOG_TITLE =
            "Choose abstraction predicates for join";

    private AbstractionPredicatesChoiceDialogController ctrl = null;
    private Goal goal = null;

    private ArrayList<Pair<Sort, Name>> registeredPlaceholders =
            new ArrayList<Pair<Sort, Name>>();

    private ArrayList<AbstractionPredicate> registeredPredicates =
            new ArrayList<AbstractionPredicate>();

    private HashMap<AbstractionPredicate, Sort> sortsForPredicates =
            new HashMap<AbstractionPredicate, Sort>();

    private Class<? extends AbstractPredicateAbstractionLattice> latticeType =
            SimplePredicateAbstractionLattice.class;

    /**
     * @return The abstraction predicates set by the user. Is null iff the user
     *         pressed cancel.
     */
    public ArrayList<AbstractionPredicate> getRegisteredPredicates() {
        return registeredPredicates;
    }

    /**
     * @return The mappings from abstraction predicates to input sorts.
     */
    public HashMap<AbstractionPredicate, Sort> getSortsForPredicates() {
        return sortsForPredicates;
    }

    /**
     * @return The chosen lattice type (class object for class that is an
     *         instance of {@link AbstractPredicateAbstractionLattice}).
     */
    public Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType;
    }

    /**
     * Constructs a new {@link AbstractionPredicatesChoiceDialog}.
     */
    private AbstractionPredicatesChoiceDialog() {
        super(MAIN_WINDOW_INSTANCE, DIALOG_TITLE, true);
        setLocation(MAIN_WINDOW_INSTANCE.getLocation());
        setSize(INITIAL_SIZE);
        setDefaultCloseOperation(DISPOSE_ON_CLOSE);

        final FXMLLoader loader = new FXMLLoader();
        final URL resource =
                AbstractionPredicatesChoiceDialog.class
                        .getResource("AbstractionPredicatesJoinDialog.fxml");

        assert resource != null : "Could not find FXML file for abstraction predicates choice dialog";

        loader.setLocation(resource);

        final JFXPanel fxPanel = new JFXPanel();
        add(fxPanel);

        Platform.setImplicitExit(false);
        final FutureTask<AbstractionPredicatesChoiceDialogController> task =
                new FutureTask<AbstractionPredicatesChoiceDialogController>(
                        new Callable<AbstractionPredicatesChoiceDialogController>() {
                            @Override
                            public AbstractionPredicatesChoiceDialogController call()
                                    throws Exception {
                                Scene scene = createScene(loader);
                                fxPanel.setScene(scene);
                                return loader.getController();
                            }
                        });

        Platform.runLater(task);
        try {
            // Set the FXML controller
            ctrl = task.get();
        }
        catch (InterruptedException | ExecutionException e) {
            // This should never happen.
            e.printStackTrace();
            return;
        }
    }

    private Scene createScene(FXMLLoader loader) {
        AnchorPane dialogLayout;
        try {
            dialogLayout = (AnchorPane) loader.load();
        }
        catch (IOException e) {
            // This should never happen.
            e.printStackTrace();
            return null;
        }

        return new Scene(dialogLayout);
    }

    /**
     * Constructs a new {@link AbstractionPredicatesChoiceDialog}. The given
     * goal is used to get information about the proof.
     *
     * @param goal
     *            The goal on which the join rule is applied.
     */
    public AbstractionPredicatesChoiceDialog(Goal goal) {
        this();
        this.goal = goal;

        final Services services = goal.proof().getServices();

        final String progVarsStr =
                goal.getGlobalProgVars().toString().replace(",", ", ");
        Platform.runLater(() -> ctrl.setAvailableProgVarsInfoTxt(progVarsStr
                .substring(1, progVarsStr.length() - 1)));

        ctrl.currentPlaceholderProperty().addListener(
                (ObservableValue<? extends String> observable, String oldValue,
                        String newValue) -> {
                    // Expecting input of type <SORT> <NAME>, where the
                    // placeholders may not contain spaces.

                    try {
                        parsePlaceholder(newValue);

                        ctrl.placeholdersProblemsListData.clear();
                    }
                    catch (Exception e) {
                        ctrl.placeholdersProblemsListData.clear();
                        ctrl.placeholdersProblemsListData.add(e.getMessage());
                    }
                });

        ctrl.currentPredicateProperty().addListener(
                (ObservableValue<? extends String> observable, String oldValue,
                        String newValue) -> {
                    try {
                        parsePredicate(newValue);

                        ctrl.predicateProblemsListData.clear();
                    }
                    catch (Exception e) {
                        ctrl.predicateProblemsListData.clear();
                        ctrl.predicateProblemsListData.add(e.getMessage());
                    }

                });

        ctrl.registerPlaceholderListListener((Change<? extends String> event) -> {
            while (event.next()) {
                if (event.wasRemoved()) {
                    Pair<Sort, Name> removedPlaceholder =
                            registeredPlaceholders.get(event.getFrom());

                    services.getNamespaces().variables()
                            .remove(removedPlaceholder.second);
                    registeredPlaceholders.remove(event.getFrom());
                }
                else if (event.wasAdded()) {
                    Pair<Sort, Name> parsed =
                            parsePlaceholder(event.getAddedSubList().get(0));

                    registeredPlaceholders.add(parsed);
                    services.getNamespaces()
                            .variables()
                            .add(new LocationVariable(new ProgramElementName(
                                    parsed.second.toString()), parsed.first));
                }
            }
        });

        ctrl.registerPredicatesListListener((Change<? extends String> event) -> {
            while (event.next()) {
                if (event.wasRemoved()) {
                    registeredPredicates.remove(event.getFrom());
                }
                else if (event.wasAdded()) {
                    AbstractionPredicate parsed;
                    try {
                        parsed = parsePredicate(event.getAddedSubList().get(0));
                    }
                    catch (Exception e) {
                        throw new RuntimeException(e);
                    }

                    registeredPredicates.add(parsed);
                }
            }
        });

        ctrl.okPressedProperty().addListener(
                (ObservableValue<? extends Boolean> observable,
                        Boolean oldValue, Boolean newValue) -> {
                    if (newValue) {
                        setVisible(false);
                        dispose();
                    }
                });

        ctrl.cancelPressedProperty().addListener(
                (ObservableValue<? extends Boolean> observable,
                        Boolean oldValue, Boolean newValue) -> {
                    if (newValue) {
                        registeredPlaceholders = null;
                        registeredPredicates = null;

                        setVisible(false);
                        dispose();
                    }
                });

        ctrl.latticeTypeProperty()
                .addListener(
                        (ObservableValue<? extends Class<? extends AbstractPredicateAbstractionLattice>> observable,
                                Class<? extends AbstractPredicateAbstractionLattice> oldValue,
                                Class<? extends AbstractPredicateAbstractionLattice> newValue) -> {
                            this.latticeType = newValue;
                        });
    }

    /**
     * Parses a placeholder using
     * {@link JoinRuleUtils#parsePlaceholder(String, Services)}.
     * 
     * @param input
     *            The input to parse.
     * @return The parsed placeholder (sort and name).
     */
    private Pair<Sort, Name> parsePlaceholder(String input) {
        return JoinRuleUtils
                .parsePlaceholder(input, goal.proof().getServices());
    }

    /**
     * Parses an abstraction predicate using
     * {@link JoinRuleUtils#parsePredicate(String, ArrayList, Services)}.
     * 
     * @param input
     *            The input to parse.
     * @return The parsed abstraction predicate.
     * @throws ParserException
     *             If there is a mistake in the input.
     */
    private AbstractionPredicate parsePredicate(String input)
            throws ParserException {
        return JoinRuleUtils.parsePredicate(input, registeredPlaceholders, goal
                .proof().getServices());
    }

    // ////////////////////////////////////// //
    // //////////// TEST METHODS //////////// //
    // ////////////////////////////////////// //

    public static void main(String[] args) {
        de.uka.ilkd.key.proof.Proof proof =
                loadProof("firstTouch/01-Agatha/project.key");

        AbstractionPredicatesChoiceDialog dialog =
                new AbstractionPredicatesChoiceDialog(proof.openGoals().head());
        dialog.setVisible(true);
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    static de.uka.ilkd.key.proof.Proof loadProof(String proofFileName) {
        java.io.File proofFile = new java.io.File("examples/" + proofFileName);

        try {
            de.uka.ilkd.key.control.KeYEnvironment<?> environment =
                    de.uka.ilkd.key.control.KeYEnvironment.load(
                            de.uka.ilkd.key.proof.init.JavaProfile
                                    .getDefaultInstance(), proofFile, null,
                            null, null, true);
            de.uka.ilkd.key.proof.Proof proof = environment.getLoadedProof();

            return proof;
        }
        catch (de.uka.ilkd.key.proof.io.ProblemLoaderException e) {
            return null;
        }
    }

}
