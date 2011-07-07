package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SimpleExceptionDialog;
import de.uka.ilkd.key.gui.lemmatagenerator.FileChooser;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmaSelectionDialog;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.LoaderListener;

public class LoadUserDefinedTacletsAction extends MainWindowAction {
    public enum Mode {ProveUserDefinedTaclets{
            @Override
        public String toString() {
               return "";
        }
    }        
            ,ProveKeYTaclets,ProveAndAddUserDefinedTaclets
    
           
    };    
    private static final long serialVersionUID = 1L;
    private final Mode mode;

    public LoadUserDefinedTacletsAction(MainWindow mainWindow,Mode mode) {
        super(mainWindow);
        this.mode = mode;
        putValue(NAME, "Load User-Defined Taclets...");
        putValue(
                SHORT_DESCRIPTION,
                    "Loads additional taclets and creates the corresponding proofs.");

        getMediator().enableWhenProof(this);
    }

    private void loadTaclets() {
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

        LoaderListener listener = new LoaderListener() {
            @Override
            public void stopped(Throwable exception) {
                // TODO: handle the exception
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

            @Override
            public void started() {
                getMediator().stopInterface(true);
            }
        };

        TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(
                    mainWindow.getUserInterface(), fileForLemmata, proof.env(), listener,
                    mainWindow.getUserInterface(), new LemmaSelectionDialog(), filesForAxioms,
                                fileForDefinitions,loadAsLemmata
                                );
        loader.start();

    }
    
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
}
