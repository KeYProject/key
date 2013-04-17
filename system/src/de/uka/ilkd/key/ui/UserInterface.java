// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.proof.ApplyTacletDialogModel;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.ProgressMonitor;

public interface UserInterface extends ProblemInitializerListener, ProverTaskListener, ProgressMonitor {

    /**
     * these methods are called immediately before automode is started to ensure that
     * the GUI can respond in a reasonable way, e.g., change the cursor to a waiting cursor
     */
    void notifyAutoModeBeingStarted();

    /**
     * these methods are called when automode has been stopped to ensure that
     * the GUI can respond in a reasonable way, e.g., change the cursor to the default
     */
    void notifyAutomodeStopped();

    /**
     * general notifications about exceptions etc.
     */
    void notify(NotificationEvent event);

    /**
     * called to complete and apply a taclet instantiations
     * @param models the  partial models with all different possible instantiations found automatically
     * @param goal the Goal where to apply
     */
    void completeAndApplyTacletMatch(ApplyTacletDialogModel[] models, Goal goal);

    /**
     * asks if removal of a task is completed. This is useful to display a dialog to the user and asking her or
     * if on command line to allow it always.
     * @param message
     * @return true if removal has been granted
     */
    boolean confirmTaskRemoval(String message);

    /**
     * loads the problem or proof from the given file
     * @param file the File with the problem description or the proof
     */
    void loadProblem(File file);

    /**
     * loads the problem or proof from the given file
     * @param file the File with the problem description or the proof
     * @param classPath the class path entries to use.
     * @param bootClassPath the boot class path to use. 
     */
    void loadProblem(File file, List<File> classPath, File bootClassPath);

    /** 
     * called to open the build in examples 
     */
    void openExamples();

    /**
     * completes rule applications of built in rules
     * @param app the DefaultBuiltInRuleApp to be completed
     * @param goal the Goal where the app will later be applied to
     * @param forced a boolean indicating if the rule should be applied without any 
     * additional interaction from the user provided that the application object can be 
     * made complete automatically
     * @return a complete app or null if no completion was possible
     */
    IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced);    

    /**
     * <p>
     * Creates a new {@link ProblemInitializer} instance which is configured
     * for this {@link UserInterface}.
     * </p>
     * <p>
     * This method is used by nearly all Eclipse based product that
     * uses KeY.
     * </p>
     * @return The instantiated {@link ProblemInitializer}.
     */
    ProblemInitializer createProblemInitializer();
    
    /**
     * Returns the used {@link KeYMediator}.
     * @return The used {@link KeYMediator}.
     */
    KeYMediator getMediator();
    
    /**
     * Opens a java file in this {@link UserInterface} and returns the instantiated {@link DefaultProblemLoader}
     * which can be used to instantiated proofs programmatically.
     * @param file The java file to open.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @return The opened {@link DefaultProblemLoader}.
     * @throws ProblemLoaderException Occurred Exception.
     */
    DefaultProblemLoader load(File file, List<File> classPaths, File bootClassPath) throws ProblemLoaderException;
    
    /**
     * Instantiates a new {@link Proof} in this {@link UserInterface} for the given
     * {@link ProofOblInput} based on the {@link InitConfig}.
     * @param initConfig The {@link InitConfig} which provides the source code.
     * @param input The description of the {@link Proof} to instantiate.
     * @return The instantiated {@link Proof}.
     * @throws ProofInputException Occurred Exception.
     */
    Proof createProof(InitConfig initConfig, ProofOblInput input) throws ProofInputException;
    
    /**
     * Checks if the auto mode of this {@link UserInterface} supports the given {@link Proof}.
     * @param proof The {@link Proof} to check.
     * @return {@code true} auto mode support proofs, {@code false} auto mode don't support proof.
     */
    boolean isAutoModeSupported(Proof proof);
    
    /**
     * Starts the auto mode for the given {@link Proof}.
     * @param proof The {@link Proof} to start auto mode of.
     */
    void startAutoMode(Proof proof);
    
    /**
     * Starts the auto mode for the given {@link Proof} and the given {@link Goal}s. 
     * @param proof The {@link Proof} to start auto mode of.
     * @param goals The {@link Goal}s to close.
     */
    void startAutoMode(Proof proof, ImmutableList<Goal> goals);
    
    /**
     * Stops the currently running auto mode.
     */
    void stopAutoMode();
    
    /**
     * Blocks the current {@link Thread} while the auto mode of this
     * {@link UserInterface} is active.
     */
    void waitWhileAutoMode();
    
    /**
     * Starts the auto mode for the given proof which must be contained
     * in this user interface and blocks the current thread until it
     * has finished.
     * @param proof The {@link Proof} to start auto mode and to wait for.
     */
    void startAndWaitForAutoMode(Proof proof);
    
    /**
     * Removes the given {@link Proof} from this {@link UserInterface}.
     * @param proof The {@link Proof} to remove.
     */
    void removeProof(Proof proof);
}