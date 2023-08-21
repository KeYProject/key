/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.util.List;
import javax.annotation.Nullable;
import javax.swing.*;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmaSelectionDialog;
import de.uka.ilkd.key.gui.lemmatagenerator.LoadUserTacletsDialog;
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

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public abstract class LemmaGenerationAction extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(LemmaGenerationAction.class);

    public enum Mode {
        ProveUserDefinedTaclets, ProveKeYTaclets, ProveAndAddUserDefinedTaclets
    }

    private static final long serialVersionUID = 1L;



    public LemmaGenerationAction(MainWindow mainWindow) {
        super(mainWindow);

        putValue(NAME, getTitle());
        putValue(SHORT_DESCRIPTION, getDescription());
        if (proofIsRequired()) {
            getMediator().enableWhenProofLoaded(this);
        }
    }

    abstract protected void loadTaclets();

    abstract protected String getTitle();

    abstract protected String getDescription();

    abstract protected boolean proofIsRequired();

    protected final void handleException(Throwable exception) {
        LOGGER.error("", exception);
        IssueDialog.showExceptionDialog(mainWindow, exception);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            loadTaclets();
        } catch (Throwable exception) {
            handleException(exception);
        }
    }

    private abstract static class AbstractLoaderListener implements LoaderListener {
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
        public final void stopped(final @Nullable ProofAggregate p,
                final ImmutableSet<Taclet> taclets,
                final boolean addAsAxioms) {
            SwingUtilities.invokeLater(() -> doStopped(p, taclets, addAsAxioms));
        }

        protected abstract void doStopped(ProofAggregate p, ImmutableSet<Taclet> taclets,
                boolean addAsAxioms);

        @Override
        public final void stopped(final Throwable exception) {
            SwingUtilities.invokeLater(() -> doStopped(exception));
        }

        protected abstract void doStopped(Throwable exception);
    }

    public static class ProveKeYTaclets extends LemmaGenerationAction {


        private static final long serialVersionUID = 1L;

        public ProveKeYTaclets(MainWindow mainWindow) {
            super(mainWindow);

        }

        @Override
        protected void loadTaclets() {

            TacletLoader tacletLoader =
                new TacletLoader.KeYsTacletsLoader(mainWindow.getUserInterface(),
                    mainWindow.getUserInterface(), mainWindow.getMediator().getProfile());


            LoaderListener listener = new AbstractLoaderListener(mainWindow) {
                @Override
                public void doStopped(Throwable exception) {
                    LOGGER.error("", exception);
                    IssueDialog.showExceptionDialog(ProveKeYTaclets.this.mainWindow, exception);
                }

                @Override
                public void doStopped(ProofAggregate p, ImmutableSet<Taclet> taclets,
                        boolean addAxioms) {
                    getMediator().startInterface(true);
                    if (p != null) {

                        mainWindow.getUserInterface().registerProofAggregate(p);
                    }

                }

            };

            TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(listener,
                new LemmaSelectionDialog(), true, tacletLoader,
                tacletLoader.getProofEnvForTaclets().getInitConfigForEnvironment(), true);
            loader.start();

        }

        @Override
        protected String getTitle() {
            return "KeY's Taclets...";
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
        private LoadUserTacletsDialog chooser;

        public ProveUserDefinedTaclets(MainWindow mainWindow) {
            super(mainWindow);
        }

        @Override
        protected void loadTaclets() {
            if (chooser == null) {
                chooser = new LoadUserTacletsDialog(LoadUserTacletsDialog.Mode.PROVE);
            }

            boolean loaded = chooser.showAsDialog();

            if (!loaded) {
                return;
            }

            final File fileForLemmata = chooser.getFileForTaclets();
            final boolean loadAsLemmata = chooser.isGenerateProofObligations();
            List<File> filesForAxioms = chooser.getFilesForAxioms();
            Profile profile = mainWindow.getMediator().getProfile();
            final ProblemInitializer problemInitializer =
                new ProblemInitializer(mainWindow.getUserInterface(), new Services(profile),
                    mainWindow.getUserInterface());

            TacletLoader tacletLoader = new TacletLoader.TacletFromFileLoader(
                mainWindow.getUserInterface(), mainWindow.getUserInterface(), problemInitializer,
                profile, fileForLemmata, filesForAxioms);



            LoaderListener listener = new AbstractLoaderListener(mainWindow) {
                @Override
                public void doStopped(Throwable exception) {
                    LOGGER.error("", exception);
                    IssueDialog.showExceptionDialog(ProveUserDefinedTaclets.this.mainWindow,
                        exception);
                }

                @Override
                public void doStopped(ProofAggregate p, ImmutableSet<Taclet> taclets,
                        boolean addAxioms) {
                    getMediator().startInterface(true);
                    if (p != null) {

                        mainWindow.getUserInterface().registerProofAggregate(p);
                    }
                }

            };

            TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(listener,
                new LemmaSelectionDialog(), loadAsLemmata, tacletLoader,
                tacletLoader.getProofEnvForTaclets().getInitConfigForEnvironment(), true);
            loader.start();

        }

        @Override
        protected String getTitle() {
            return "User-Defined Taclets...";
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

    static public class ProveAndAddTaclets extends LemmaGenerationAction {
        public ProveAndAddTaclets(MainWindow mainWindow) {
            super(mainWindow);
        }

        private static final long serialVersionUID = 1L;

        @Override
        protected void loadTaclets() {
            LoadUserTacletsDialog chooser =
                new LoadUserTacletsDialog(LoadUserTacletsDialog.Mode.LOAD);

            boolean loaded = chooser.showAsDialog();

            if (!loaded) {
                return;
            }
            final Proof proof = getMediator().getSelectedProof();
            final File fileForLemmata = chooser.getFileForTaclets();
            final boolean loadAsLemmata = chooser.isGenerateProofObligations();
            List<File> filesForAxioms = chooser.getFilesForAxioms();
            final ProblemInitializer problemInitializer =
                new ProblemInitializer(mainWindow.getUserInterface(),
                    new Services(proof.getServices().getProfile()), mainWindow.getUserInterface());

            TacletLoader tacletLoader = new TacletLoader.TacletFromFileLoader(
                mainWindow.getUserInterface(), mainWindow.getUserInterface(), problemInitializer,
                fileForLemmata, filesForAxioms, proof.getInitConfig().copy());



            LoaderListener listener = new AbstractLoaderListener(mainWindow) {
                @Override
                public void doStopped(Throwable exception) {
                    LOGGER.error("", exception);
                    IssueDialog.showExceptionDialog(ProveAndAddTaclets.this.mainWindow, exception);
                }

                @Override
                public void doStopped(ProofAggregate p, ImmutableSet<Taclet> taclets,
                        boolean addAxioms) {
                    getMediator().startInterface(true);
                    if (p != null) {
                        mainWindow.getUserInterface().registerProofAggregate(p);
                    }

                    if (p != null || addAxioms) {
                        // add only the taclets to the goals if
                        // the proof obligations were added successfully.
                        ImmutableList<Taclet> base = proof.getInitConfig().getTaclets();
                        base = base.prependReverse(taclets);
                        proof.getInitConfig().setTaclets(base);
                        for (Taclet taclet : taclets) {
                            for (Goal goal : proof.openGoals()) {
                                goal.addTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
                                    false);
                            }
                        }
                    }
                }

            };

            TacletSoundnessPOLoader loader =
                new TacletSoundnessPOLoader(listener, new LemmaSelectionDialog(), loadAsLemmata,
                    tacletLoader, proof.getInitConfig(), false);
            loader.start();

        }

        @Override
        protected String getTitle() {
            return "Load User-Defined Taclets...";
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
