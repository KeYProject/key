// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.core.Main;
import static de.uka.ilkd.key.core.Main.Verbosity.HIGH;
import static de.uka.ilkd.key.core.Main.Verbosity.SILENT;
import de.uka.ilkd.key.core.TaskFinishedInfo;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import static de.uka.ilkd.key.ui.AbstractUserInterface.fileName;
import de.uka.ilkd.key.util.Pair;
import java.io.File;
import java.io.IOException;

/**
 * Implementation of {@link UserInterface} used by command line interface of
 * KeY.
 */
public class ConsoleUserInterface extends AbstractConsoleUserInterface {
    
    // flag to indicate that a file should merely be loaded not proved. (for
    // "reload" testing)
    private final boolean loadOnly;
    
    
    /**
     * Current key problem file that is attempted to be proven.
     */
    private File keyProblemFile = null;
    
    /**
     * We want to record whether there was a proof that could not be proven.
     * {@link Main} calls System.exit() after all files have been loaded with
     * {@link #loadProblem(java.io.File)}. Program return value depends on
     * whether there has been a proof attempt that was not successful.
     */
    public boolean allProofsSuccessful = true;
    
    public ConsoleUserInterface(byte verbosity, boolean loadOnly) {
        super(verbosity);
        this.loadOnly = loadOnly;
    }

    public ConsoleUserInterface(boolean verbose, boolean loadOnly) {
        super(verbose);
        this.loadOnly = loadOnly;
    }

   private void printResults(final int openGoals,
                                  TaskFinishedInfo info,
                                  final Object result2) {
       if (verbosity >= HIGH) {
           System.out.println("]"); // end progress bar
       }
       if (verbosity > SILENT) {
           System.out.println("[ DONE  ... rule application ]");
           if (verbosity >= HIGH) {
               System.out.println("\n== Proof "+ (openGoals > 0 ? "open": "closed")+ " ==");
               final Proof.Statistics stat = info.getProof().statistics();
               System.out.println("Proof steps: "+stat.nodes);
               System.out.println("Branches: "+stat.branches);
               System.out.println("Automode Time: "+stat.autoModeTime+"ms");
               System.out.println("Time per step: "+stat.timePerStep+"ms");
           }
           System.out.println("Number of goals remaining open: " + openGoals);
           System.out.flush();
       }
       // this seems to be a good place to free some memory
       Runtime.getRuntime().gc();

       /*
        * It is assumed that this part of the code is never reached, unless a 
        * value has been assigned to keyProblemFile in method loadProblem(File).
        */
       assert keyProblemFile != null : "Unexcpected null pointer. Trying to"
               + " save a proof but no corresponding key problem file is "
               + "available.";
       allProofsSuccessful &= BatchMode.saveProof(result2, info.getProof(), keyProblemFile);
       /*
        * We "delete" the value of keyProblemFile at this point by assigning
        * null to it. That way we prevent KeY from saving another proof (that
        * belongs to another key problem file) for a key problem file whose
        * execution cycle has already been finished (and whose proof has
        * already been saved). It is assumed that a new value has been assigned
        * beforehand in method loadProblem(File), if this part of the code is
        * reached again.
        */
       keyProblemFile = null;
   }

    @Override
   public void taskFinished(TaskFinishedInfo info) {
       progressMax = 0; // reset progress bar marker
       final Proof proof = info.getProof();
       if (proof==null) {
           if (verbosity > SILENT) {
               System.out.println("Proof loading failed");
               final Object error = info.getResult();
               if (error instanceof Throwable) {
                   ((Throwable) error).printStackTrace();
               }
           }
           System.exit(1);
       }
       final int openGoals = proof.openGoals().size();
       final Object result2 = info.getResult();
       if (info.getSource() instanceof ApplyStrategy ||
           info.getSource() instanceof ProofMacro) {
           if (numOfInvokedMacros == 0) {
               printResults(openGoals, info, result2);
           } else if (!macroChosen()) {
               finish(proof);
           }
       } else if (info.getSource() instanceof ProblemLoader) {
           if (verbosity > SILENT) System.out.println("[ DONE ... loading ]");
           if (result2 != null) {
               if (verbosity > SILENT) System.out.println(result2);
               if (verbosity >= HIGH && result2 instanceof Throwable) {
                   ((Throwable) result2).printStackTrace();
               }
               System.exit(-1);
           }
           if(loadOnly ||  openGoals==0) {
               if (verbosity > SILENT)
                   System.out.println("Number of open goals after loading: " +
                           openGoals);
               System.exit(0);
           }
           if (macroChosen()) {
               applyMacro();
           } else {
               finish(proof);
           }
       }
   }

    @Override
    public void taskStarted(String message, int size) {
        progressMax = size;
        if (verbosity >= HIGH) {
            if (ApplyStrategy.PROCESSING_STRATEGY.equals(message)) {
                System.out.print(message+" ["); // start progress bar
            } else {
                System.out.println(message);
            }
        }
    }

    @Override
    public void loadProblem(File file) {
        /*
         * Current file is stored in a private field.
         * It will be used in method printResults() to determine file names,
         * in which proofs will be written.
         */
        keyProblemFile = file;
        super.loadProblem(file);
    }

   @Override
   public File saveProof(Proof proof, String fileExtension) {
       if (loadOnly) {
           return null;
       }
       final Pair<File, String> f = fileName(proof, fileExtension);
       File file = f.first;
       assert file != null : "No corresponding filename available for proof";
       String defaultName = f.second;

       final String recDir = file.getParent();
       file = (defaultName != null) ? new File(recDir, defaultName): file;

       String poDir =
               file.getParent().endsWith("src") ?
                       new File(file.getParent()).getParent()
                       : file.getParent();
       String proofDir = file.getParent();
       file = new File(fileExtension.equals(".key") ? poDir : proofDir, file.getName());
       ProofSaver saver = new ProofSaver(proof, file.getAbsolutePath(), Main.INTERNAL_VERSION);
       try {
           saver.save();
       } catch (IOException e) {
           e.printStackTrace();
       } catch (Exception e) {
           e.printStackTrace();
       }
       return file;
   }

    @Override
    public void proofRegistered(ProofEnvironmentEvent event) {
        mediator.setProof(event.getProofList().getFirstProof());
        proofStack = proofStack.prepend(event.getProofList().getFirstProof());
    }
}
