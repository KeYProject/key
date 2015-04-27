package de.uka.ilkd.key.proof.io;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.ProgressMonitor;

/**
 * Allows to observe and control the loading performed by an {@link AbstractProblemLoader}.
 * @author Martin Hentschel
 */
public interface ProblemLoaderControl extends ProblemInitializerListener, ProgressMonitor {
   /**
    * The loading has started.
    * @param loader The source {@link AbstractProblemLoader}.
    */
   void loadingStarted(AbstractProblemLoader loader);

   /**
    * The loading has stopped.
    * @param loader The source {@link AbstractProblemLoader}.
    * @param poContainer The loaded {@link LoadedPOContainer}.
    * @param proofList The created {@link ProofAggregate}.
    * @param result The occurred {@link ReplayResult}.
    * @throws ProblemLoaderException Occurred Exception.
    */
   void loadingFinished(AbstractProblemLoader loader, 
                        LoadedPOContainer poContainer, 
                        ProofAggregate proofList, 
                        ReplayResult result) throws ProblemLoaderException;

   /**
    * This method is called if no {@link LoadedPOContainer} was created
    * via {@link #createProofObligationContainer()} and can be overwritten
    * for instance to open the proof management dialog as done by {@link ProblemLoader}.
    * @return true if the proof obligation was selected, and false if action was aborted
    */
    boolean selectProofObligation(InitConfig initConfig);

    /**
     * Report the occurred warnings.
     * @param warnings The occurred warnings.
     */
    void reportWarnings(ImmutableSet<PositionedString> warnings);
}
