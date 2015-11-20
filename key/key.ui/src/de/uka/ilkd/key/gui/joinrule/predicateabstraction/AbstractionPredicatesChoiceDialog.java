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
import java.io.File;
import java.io.IOException;
import java.io.StringReader;
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

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.axiom_abstraction.AbstractionPredicate;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class AbstractionPredicatesChoiceDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    private final static MainWindow MAIN_WINDOW_INSTANCE = MainWindow
            .getInstance();

    /** The initial size of this dialog. */
    private static final Dimension INITIAL_SIZE = new Dimension(850, 450);

    private static final String DIALOG_TITLE =
            "Choose abstraction predicates for join";

    private AbstractionPredicatesJoinDialogController ctrl = null;
    private Goal goal = null;

    private ArrayList<Pair<Sort, Name>> registeredPlaceholders =
            new ArrayList<Pair<Sort, Name>>();

    private ArrayList<AbstractionPredicate> registeredPredicates =
            new ArrayList<AbstractionPredicate>();

    private HashMap<AbstractionPredicate, Sort> sortsForPredicates =
            new HashMap<AbstractionPredicate, Sort>();

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
     * TODO: Document.
     */
    private AbstractionPredicatesChoiceDialog() {
        super(MAIN_WINDOW_INSTANCE, DIALOG_TITLE, true);
        setLocation(MAIN_WINDOW_INSTANCE.getLocation());
        setSize(INITIAL_SIZE);
        setDefaultCloseOperation(DISPOSE_ON_CLOSE);

        final FXMLLoader loader = new FXMLLoader();
        loader.setLocation(AbstractionPredicatesChoiceDialog.class
                .getResource("AbstractionPredicatesJoinDialog.fxml"));

        final JFXPanel fxPanel = new JFXPanel();
        add(fxPanel);

        final FutureTask<AbstractionPredicatesJoinDialogController> task =
                new FutureTask<AbstractionPredicatesJoinDialogController>(
                        new Callable<AbstractionPredicatesJoinDialogController>() {
                            @Override
                            public AbstractionPredicatesJoinDialogController call()
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
     * TODO: Document.
     *
     * @param goal
     */
    public AbstractionPredicatesChoiceDialog(Goal goal) {
        this();
        this.goal = goal;

        final Services services = goal.proof().getServices();

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
    }

    /**
     * TODO: Document.
     *
     * @return
     */
    private static AbbrevMap getAbbrevMap() {
        return MainWindow.getInstance().getMediator().getNotationInfo()
                .getAbbrevMap();
    }

    /**
     * 
     * TODO: Document.
     *
     * @param input
     * @return
     */
    private Pair<Sort, Name> parsePlaceholder(String input) {
        final Services services = goal.proof().getServices();

        String[] chunks = input.split(" ");
        if (chunks.length != 2) {
            throw new RuntimeException(
                    "Expecting an input of type &lt;SORT&gt; &lt;NAME&gt;");
        }

        Sort sort = (Sort) services.getNamespaces().sorts().lookup(chunks[0]);

        if (sort == null) {
            throw new RuntimeException("Sort \"" + chunks[0]
                    + "\" is not known");
        }

        String strName = chunks[1];
        Name name = new Name(strName);

        if (services.getNamespaces().lookup(name) != null) {
            throw new RuntimeException("The name \"" + strName
                    + "\" is already known to the system.<br/>"
                    + "Plase choose a fresh one.");
        }

        return new Pair<Sort, Name>(sort, name);
    }

    /**
     * TODO: Document.
     *
     * @param input
     * @return
     * @throws ParserException
     */
    private AbstractionPredicate parsePredicate(String input)
            throws ParserException {
        final Services services = goal.proof().getServices();
        final TermBuilder tb = services.getTermBuilder();
        final TermFactory tf = services.getTermFactory();

        DefaultTermParser parser = new DefaultTermParser();
        Term formula =
                parser.parse(new StringReader(input), Sort.FORMULA, services,
                        services.getNamespaces(), getAbbrevMap());

        ImmutableSet<LocationVariable> containedLocVars =
                JoinRuleUtils.getLocationVariables(formula, services);

        int nrContainedPlaceholders = 0;
        LocationVariable usedPlaceholder = null;
        for (Pair<Sort, Name> placeholder : registeredPlaceholders) {
            LocationVariable placeholderVariable =
                    (LocationVariable) services.getNamespaces().variables()
                            .lookup(placeholder.second);

            if (containedLocVars.contains(placeholderVariable)) {
                nrContainedPlaceholders++;
                usedPlaceholder = placeholderVariable;
            }
        }

        if (nrContainedPlaceholders != 1) {
            throw new RuntimeException(
                    "An abstraction predicate must contain exactly one placeholder.");
        }

        final LocationVariable fUsedPlaceholder = usedPlaceholder;
        final Sort fInputSort = usedPlaceholder.sort();

        return AbstractionPredicate.create(formula.toString(), fInputSort, (
                Term param) -> {
            if (param.sort() != fInputSort) {
                throw new IllegalArgumentException("Input must be of sort \""
                        + fInputSort + "\", given: \"" + param.sort() + "\".");
            }

            return OpReplacer.replace(tb.var(fUsedPlaceholder), param, formula,
                    tf);
        });
    }

    // ////////////////////////////////////// //
    // //////////// TEST METHODS //////////// //
    // ////////////////////////////////////// //

    /**
     * TODO: Document.
     *
     * @param args
     */
    public static void main(String[] args) {
        Proof proof = loadProof("firstTouch/01-Agatha/project.key");

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
    static Proof loadProof(String proofFileName) {
        File proofFile = new File("examples/" + proofFileName);

        try {
            KeYEnvironment<?> environment =
                    KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                            proofFile, null, null, null, true);
            Proof proof = environment.getLoadedProof();

            return proof;
        }
        catch (ProblemLoaderException e) {
            return null;
        }
    }

}
