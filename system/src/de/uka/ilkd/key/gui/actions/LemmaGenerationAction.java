package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SimpleExceptionDialog;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.lemmatagenerator.EnvironmentCreator;
import de.uka.ilkd.key.gui.lemmatagenerator.FileChooser;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmaSelectionDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.LoaderListener;
import de.uka.ilkd.key.taclettranslation.lemma.TacletLoader;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.key.util.ProgressMonitor;

public abstract class LemmaGenerationAction extends MainWindowAction {
    public enum Mode {ProveUserDefinedTaclets,ProveKeYTaclets,ProveAndAddUserDefinedTaclets};    
    private static final long serialVersionUID = 1L;


    
    
    public LemmaGenerationAction(MainWindow mainWindow) {
        super(mainWindow);

        putValue(NAME,getTitle());
        putValue(SHORT_DESCRIPTION,getDescription());
        if(proofIsRequired()){
                getMediator().enableWhenProof(this);
        }
    }

    abstract protected void loadTaclets();
    abstract protected String getTitle();
    abstract protected String getDescription();
    abstract protected boolean proofIsRequired();
    
    private void handleException(Throwable exception){
        String desc = exception.getMessage();
        SimpleExceptionDialog.INSTANCE.showDialog("Error while loading taclets:", desc, exception); 
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            loadTaclets();        
        } catch(Throwable exception) {
              handleException(exception);  
        }
    }
    
    private abstract class AbstractLoaderListener implements LoaderListener{
            @Override
            public void started() {
                getMediator().stopInterface(true);
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
    }
    
    static public class ProveKeYTaclets extends LemmaGenerationAction{

        public ProveKeYTaclets(MainWindow mainWindow) {
                super(mainWindow);
               
        }
        
        @Override
        protected void loadTaclets() {
                System.out.println("START");
                TacletLoader tacletLoader = new TacletLoader.KeYsTacletsLoader(mainWindow.getUserInterface(),mainWindow.getUserInterface(),
                                mainWindow.getMediator().getProfile());
                System.out.println("taclet loader created");
                LoaderListener listener = new AbstractLoaderListener() {
                        @Override
                        public void stopped(Throwable exception) {
                              throw new RuntimeException(exception);
                        }

                        @Override
                        public void stopped(ProofAggregate p,
                                    ImmutableSet<Taclet> taclets, boolean addAxioms) {
                            getMediator().startInterface(true);
                            if (p != null) {

                                mainWindow.addProblem(p);
                            }
                            
                        }

                    };
                    
                    TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(
                                 listener,
                                new LemmaSelectionDialog(),true,tacletLoader,true);
                    System.out.println("start loading pos");
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
    
    static public class ProveUserDefinedTaclets extends LemmaGenerationAction{

        public ProveUserDefinedTaclets(MainWindow mainWindow) {
                super(mainWindow);
        }

        @Override
        protected void loadTaclets() {
                FileChooser chooser = new FileChooser();

                boolean loaded = chooser.showAsDialog();

                if (!loaded) {
                    return;
                }
          
                final File fileForLemmata = chooser.getFileForLemmata();
                final File fileForDefinitions = chooser.getFileForDefinitions();
                final boolean loadAsLemmata = chooser.isLoadingAsLemmata();
                List<File> filesForAxioms = chooser.getFilesForAxioms();
                final ProblemInitializer problemInitializer = new ProblemInitializer(mainWindow.getUserInterface(),
                                mainWindow.getMediator().getProfile(), new Services(
                                                new KeYRecoderExcHandler()),
                                false, mainWindow.getUserInterface());
                
                TacletLoader tacletLoader = new TacletLoader.TacletFromFileLoader(mainWindow.getUserInterface(),
                                                      mainWindow.getUserInterface(),
                                                      problemInitializer,
                                                      mainWindow.getMediator().getProfile(),
                                                      fileForDefinitions ,
                                                      fileForLemmata,
                                                      filesForAxioms,
                                                      null);
               
                
                

                LoaderListener listener = new AbstractLoaderListener() {
                    @Override
                    public void stopped(Throwable exception) {
                          throw new RuntimeException(exception);
                    }

                    @Override
                    public void stopped(ProofAggregate p,
                                ImmutableSet<Taclet> taclets, boolean addAxioms) {
                        getMediator().startInterface(true);
                        if (p != null) {

                            mainWindow.addProblem(p);
                        }                        
                    }

                };
                
                TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(
                             listener,
                            new LemmaSelectionDialog(),loadAsLemmata,tacletLoader,true);
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
                FileChooser chooser = new FileChooser();

                boolean loaded = chooser.showAsDialog();

                if (!loaded) {
                    return;
                }
                final Proof proof = getMediator().getSelectedProof();
                final File fileForLemmata = chooser.getFileForLemmata();
                final File fileForDefinitions = chooser.getFileForDefinitions();
                final boolean loadAsLemmata = chooser.isLoadingAsLemmata();
                List<File> filesForAxioms = chooser.getFilesForAxioms();
                final ProblemInitializer problemInitializer = new ProblemInitializer(mainWindow.getUserInterface(),
                                proof.env().getInitConfig().getProfile(), new Services(
                                                new KeYRecoderExcHandler()),
                                false, mainWindow.getUserInterface());
                
                TacletLoader tacletLoader = new TacletLoader.TacletFromFileLoader(mainWindow.getUserInterface(),
                                                      mainWindow.getUserInterface(),
                                                      problemInitializer,
                                                      mainWindow.getMediator().getProfile(),
                                                      fileForDefinitions ,
                                                      fileForLemmata,
                                                      filesForAxioms,
                                                      proof.env());
               

                

                LoaderListener listener = new AbstractLoaderListener() {
                    @Override
                    public void stopped(Throwable exception) {
                          throw new RuntimeException(exception);
                    }

                    @Override
                    public void stopped(ProofAggregate p,
                                ImmutableSet<Taclet> taclets, boolean addAxioms) {
                        getMediator().startInterface(true);
                        if (p != null) {

                            mainWindow.addProblem(p);
                        }
                        if(p != null || addAxioms){
                            // add only the taclets to the goals if
                            // the proof obligations were added successfully.
                            ImmutableSet<Taclet> base =
                                                        proof.env().getInitConfig()
                                                                .getTaclets();
                            base = base.union(taclets);
                            proof.env().getInitConfig().setTaclets(base);
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
                            new LemmaSelectionDialog(),loadAsLemmata,tacletLoader,false);
                loader.start();

            }

        @Override
        protected String getTitle() {
                 return "Load User-Defined Taclets...";
        }

        @Override
        protected String getDescription() {
                return "Loads additional taclets and creates the corresponding proof...";
        }

        @Override
        protected boolean proofIsRequired() {
                return true;
        }
    }
}
