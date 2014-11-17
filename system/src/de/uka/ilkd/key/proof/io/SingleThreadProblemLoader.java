package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * This single threaded problem loader is used by the Eclipse integration of KeY.
 * @author Martin Hentschel
 */
public class SingleThreadProblemLoader extends AbstractProblemLoader {
   /**
    * Constructor.
    * @param file The file or folder to load.
    * @param classPath The optional class path entries to use.
    * @param bootClassPath An optional boot class path.
    * @param profileOfNewProofs The {@link Profile} to use for new {@link Proof}s.
    * @param mediator The {@link KeYMediator} to use.
    * @param askUiToSelectAProofObligationIfNotDefinedByLoadedFile {@code true} to call {@link UserInterface#selectProofObligation(InitConfig)} if no {@link Proof} is defined by the loaded proof or {@code false} otherwise which still allows to work with the loaded {@link InitConfig}.
    */
   public SingleThreadProblemLoader(File file, 
                                    List<File> classPath, 
                                    File bootClassPath, 
                                    Profile profileOfNewProofs, 
                                    KeYMediator mediator, 
                                    boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile, 
                                    Properties poPropertiesToForce) {
      super(file, classPath, bootClassPath, profileOfNewProofs, mediator, askUiToSelectAProofObligationIfNotDefinedByLoadedFile, poPropertiesToForce);
   }
}
