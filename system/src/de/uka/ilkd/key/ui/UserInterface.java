package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.proof.ApplyTacletDialogModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.ProgressMonitor;

public interface UserInterface extends ProblemInitializerListener,
        ProverTaskListener, ProgressMonitor {

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
     * @param forced TODO
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
}
