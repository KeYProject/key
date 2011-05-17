package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.MainWindow;
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

    private static final long serialVersionUID = 1L;

    public LoadUserDefinedTacletsAction(MainWindow mainWindow) {
        super(mainWindow);
        putValue(NAME, "Load User-Defined Taclets...");
        putValue(
                SHORT_DESCRIPTION,
                    "Loads additional taclets and creates the corresponding proofs.");

        getMediator().enableWhenProof(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        FileChooser chooser = new FileChooser();

        boolean loaded = chooser.showAsDialog();

        if (!loaded) {
            return;
        }
        final Proof proof = getMediator().getSelectedProof();
        final File fileForLemmata = chooser.getFileForLemmata();
        final File fileForDefinitions = chooser.getFileForDefinitions();

        List<File> filesForAxioms = chooser.getFilesForAxioms();

        LoaderListener listener = new LoaderListener() {
            @Override
            public void stopped(Throwable exception) {
                // TODO: handle the exception
                throw new RuntimeException(exception);
            }

            @Override
            public void stopped(ProofAggregate p,
                        ImmutableSet<Taclet> taclets) {
                getMediator().startInterface(true);
                if (p != null) {

                    mainWindow.addProblem(p);
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
                                fileForDefinitions);
        loader.start();

    }

}
