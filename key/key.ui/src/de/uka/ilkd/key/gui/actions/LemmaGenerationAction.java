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

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.util.List;

import javax.swing.SwingUtilities;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.lemmatagenerator.FileChooser;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmaSelectionDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.taclettranslation.lemma.TacletLoader;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.LoaderListener;

public abstract class LemmaGenerationAction extends MainWindowAction {
    public enum Mode {ProveUserDefinedTaclets,ProveKeYTaclets,ProveAndAddUserDefinedTaclets}

    private static final long serialVersionUID = 1L;


    
    
    public LemmaGenerationAction(MainWindow mainWindow) {
        super(mainWindow);

        putValue(NAME,getTitle());
        putValue(SHORT_DESCRIPTION,getDescription());
        if(proofIsRequired()){
                getMediator().enableWhenProofLoaded(this);
        }
    }

    abstract protected void loadTaclets();
    abstract protected String getTitle();
    abstract protected String getDescription();
    abstract protected boolean proofIsRequired();
    
    protected final void handleException(Throwable exception){
        ExceptionDialog.showDialog(mainWindow, exception);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            loadTaclets();        
        } catch(Throwable exception) {
              handleException(exception);  
        }
    }
    
    private abstract static class AbstractLoaderListener implements LoaderListener{
        private final MainWindow mainWindow;
        
        
            
        private AbstractLoaderListener(MainWindow mainWindow) {
                super();
                this.mainWindow = mainWindow;
        }

        @Override
            public void started() {
                mainWindow.getMediator().stopInterface(true);
            }

        @Override
        public void progressStarted(Object sender) {
                mainWindow.getUserInterface().progressStarted(sender);                        
        }

        @Override
        public void reportStatus(Object sender, String status) {
                mainWindow.getUserInterface().reportStatus(sender, status);
        }

        @Override
        public void resetStatus(Object sender) {
                mainWindow.getUserInterface().resetStatus(sender);
        }

      @Override
      public final void stopped(final ProofAggregate p, final ImmutableSet<Taclet> taclets, final boolean addAsAxioms) {
         SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
               doStopped(p, taclets, addAsAxioms);
            }
         });
      }
      
      protected abstract void doStopped(ProofAggregate p, ImmutableSet<Taclet> taclets, boolean addAsAxioms);

      @Override
      public final void stopped(final Throwable exception) {
         SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
               doStopped(exception);
            }
         });
      }
      
      protected abstract void doStopped(Throwable exception);
    }
    
    public static class ProveKeYTaclets extends LemmaGenerationAction{


        private static final long serialVersionUID = 1L;

        public ProveKeYTaclets(MainWindow mainWindow) {
                super(mainWindow);
               
        }
        
        @Override
        protected void loadTaclets() {

                TacletLoader tacletLoader = new TacletLoader.KeYsTacletsLoader(mainWindow.getUserInterface(),mainWindow.getUserInterface(),
                                mainWindow.getMediator().getProfile());
                
                
                LoaderListener listener = new AbstractLoaderListener(mainWindow) {
                        @Override
                        public void doStopped(Throwable exception) {
                                ExceptionDialog.showDialog(ProveKeYTaclets.this.mainWindow, exception);
                        }

                        @Override
                        public void doStopped(ProofAggregate p,
                                    ImmutableSet<Taclet> taclets, boolean addAxioms) {
                            getMediator().startInterface(true);
                            if (p != null) {

                               mainWindow.getUserInterface().registerProofAggregate(p);
                            }
                            
                        }

                    };
                    
                    TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(
                                 listener,
                                new LemmaSelectionDialog(),true, tacletLoader, 
                                tacletLoader.getProofEnvForTaclets().getInitConfigForEnvironment(), 
                                true);
                    loader.start();

            }

        @Override
        protected String getTitle() {
                return "KeY's Taclets";
        }

        @Override
        protected String getDescription() {
                
                return "Creates a proof obligation for some selected taclets.";
        }

        @Override
        protected boolean proofIsRequired() {
                return false;
        }
            
    }
    
    static public class ProveUserDefinedTaclets extends LemmaGenerationAction {

        private static final long serialVersionUID = 1L;
        private FileChooser chooser;

        public ProveUserDefinedTaclets(MainWindow mainWindow) {
                super(mainWindow);
        }

        @Override
        protected void loadTaclets() {
                if(chooser == null) {
                    chooser = new FileChooser(FileChooser.Mode.PROOF);
                }

                boolean loaded = chooser.showAsDialog();

                if (!loaded) {
                    return;
                }
          
                final File fileForLemmata = chooser.getFileForTaclets();
                final boolean loadAsLemmata = chooser.isGenerateProofObligations();
                List<File> filesForAxioms = chooser.getFilesForAxioms();
                Profile profile = mainWindow.getMediator().getProfile();
                final ProblemInitializer problemInitializer = new ProblemInitializer(mainWindow.getUserInterface(),
                                new Services(profile),
                                mainWindow.getUserInterface());
                
                TacletLoader tacletLoader = new TacletLoader.TacletFromFileLoader(mainWindow.getUserInterface(),
                                                      mainWindow.getUserInterface(),
                                                      problemInitializer,
                                                      profile,
                                                      fileForLemmata,
                                                      filesForAxioms);
               
                
                

                LoaderListener listener = new AbstractLoaderListener(mainWindow) {
                    @Override
                    public void doStopped(Throwable exception) {
                            ExceptionDialog.showDialog(ProveUserDefinedTaclets.this.mainWindow, exception);
                    }

                    @Override
                    public void doStopped(ProofAggregate p,
                                ImmutableSet<Taclet> taclets, boolean addAxioms) {
                        getMediator().startInterface(true);
                        if (p != null) {

                           mainWindow.getUserInterface().registerProofAggregate(p);
                        }                        
                    }

                };
                
                TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(
                             listener,
                            new LemmaSelectionDialog(),loadAsLemmata,tacletLoader,
                            tacletLoader.getProofEnvForTaclets().getInitConfigForEnvironment(),
                            true);
                loader.start();

            }

        @Override
        protected String getTitle() {
               return "User-Defined Taclets";
        }

        @Override
        protected String getDescription() {
                return "Loads user-defined taclets and creates the corresponding proof obligations.";
        }

        @Override
        protected boolean proofIsRequired() {
                return false;
        }
            
    }
    
    static public class ProveAndAddTaclets extends LemmaGenerationAction{
        public ProveAndAddTaclets(MainWindow mainWindow) {
                super(mainWindow);
        }
        private static final long serialVersionUID = 1L;

        @Override
        protected void loadTaclets() {
                FileChooser chooser = new FileChooser(FileChooser.Mode.LOAD);

                boolean loaded = chooser.showAsDialog();

                if (!loaded) {
                    return;
                }
                final Proof proof = getMediator().getSelectedProof();
                final File fileForLemmata = chooser.getFileForTaclets();
                final boolean loadAsLemmata = chooser.isGenerateProofObligations();
                List<File> filesForAxioms = chooser.getFilesForAxioms();
                final ProblemInitializer problemInitializer = new ProblemInitializer(mainWindow.getUserInterface(),
                                new Services(proof.getServices().getProfile()),
                                mainWindow.getUserInterface());
                
                TacletLoader tacletLoader = new TacletLoader.TacletFromFileLoader(mainWindow.getUserInterface(),
                                                      mainWindow.getUserInterface(),
                                                      problemInitializer,
                                                      fileForLemmata,
                                                      filesForAxioms,
                                                      proof.getInitConfig().copy());
               

                

                LoaderListener listener = new AbstractLoaderListener(mainWindow) {
                    @Override
                    public void doStopped(Throwable exception) {
                           ExceptionDialog.showDialog(ProveAndAddTaclets.this.mainWindow, exception);
                     }

                    @Override
                    public void doStopped(ProofAggregate p,
                                ImmutableSet<Taclet> taclets, boolean addAxioms) {
                        getMediator().startInterface(true);
                        if (p != null) {
                            mainWindow.getUserInterface().registerProofAggregate(p);
                        }

                        if(p != null || addAxioms){
                            // add only the taclets to the goals if
                            // the proof obligations were added successfully.
                            ImmutableSet<Taclet> base =
                                    proof.getInitConfig()
                                    .getTaclets();
                            base = base.union(taclets);
                            proof.getInitConfig().setTaclets(base);
                            for (Taclet taclet : taclets) {
                                for (Goal goal : proof.openGoals()) {
                                    goal
                                    .addTaclet(
                                            taclet,
                                            SVInstantiations.EMPTY_SVINSTANTIATIONS,
                                            false);
                                }
                            }
                        }
                    }

                };
                
                TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(
                            listener,
                            new LemmaSelectionDialog(),
                            loadAsLemmata,tacletLoader,
                            proof.getInitConfig(), false);
                loader.start();

            }

        @Override
        protected String getTitle() {
                 return "Load User-Defined Taclets";
        }

        @Override
        protected String getDescription() {
                return "Loads additional taclets and creates the corresponding proof.";
        }

        @Override
        protected boolean proofIsRequired() {
                return true;
        }
    }
}