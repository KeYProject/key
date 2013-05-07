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

//package de.uka.ilkd.key.gui.actions;
//
//import java.awt.event.ActionEvent;
//import java.io.File;
//import java.util.List;
//
//import de.uka.ilkd.key.collection.ImmutableSet;
//import de.uka.ilkd.key.gui.MainWindow;
//import de.uka.ilkd.key.gui.SimpleExceptionDialog;
//import de.uka.ilkd.key.gui.lemmatagenerator.FileChooser;
//import de.uka.ilkd.key.gui.lemmatagenerator.LemmaSelectionDialog;
//import de.uka.ilkd.key.proof.Proof;
//import de.uka.ilkd.key.proof.ProofAggregate;
//import de.uka.ilkd.key.rule.Taclet;
//import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader;
//import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.LoaderListener;
//import de.uka.ilkd.key.taclettranslation.lemma.TacletFromFileLoader;
//
//public class ProveTacletsAction extends MainWindowAction{
//        private static final long serialVersionUID = 1L;
//
//        public ProveTacletsAction(MainWindow mainWindow) {
//                super(mainWindow);
//                putValue(NAME, "Prove Taclets...");
//                putValue(
//                        SHORT_DESCRIPTION,
//                            "Creates for Taclets a proof obligation.");
//        }
//
//        private void loadTaclets() {
//                FileChooser chooser = new FileChooser();
//
//                boolean loaded = chooser.showAsDialog();
//
//                if (!loaded) {
//                    return;
//                }
//                final Proof proof = getMediator().getSelectedProof();
//                final File fileForLemmata = chooser.getFileForLemmata();
//                final File fileForDefinitions = chooser.getFileForDefinitions();
//                final boolean loadAsLemmata = chooser.isLoadingAsLemmata();
//
//                List<File> filesForAxioms = chooser.getFilesForAxioms();
//
//                LoaderListener listener = new LoaderListener() {
//                    @Override
//                    public void stopped(Throwable exception) {
//                         throw new RuntimeException(exception);
//                    }
//
//                    @Override
//                    public void stopped(ProofAggregate p,
//                                ImmutableSet<Taclet> taclets, boolean addAxioms) {
//                        getMediator().startInterface(true);
//                        if (p != null) {
//
//                            mainWindow.addProblem(p);
//                        }
//                    }
//
//                    @Override
//                    public void started() {
//                        getMediator().stopInterface(true);
//                    }
//
//                @Override
//                public void progressStarted(Object sender) {
//                        // TODO Auto-generated method stub
//                        
//                }
//
//                @Override
//                public void reportStatus(Object sender, String string) {
//                        // TODO Auto-generated method stub
//                        
//                }
//
//                @Override
//                public void resetStatus(Object sender) {
//                        // TODO Auto-generated method stub
//                        
//                }
//                };
//
//                TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(
//                            mainWindow.getUserInterface(), fileForLemmata, proof.env(), listener,
//                            mainWindow.getUserInterface(), new LemmaSelectionDialog(), filesForAxioms,
//                                        fileForDefinitions,loadAsLemmata,TacletFromFileLoader.INSTANCE
//                                        );
//                loader.start();
//
//            }
//            
//            private void handleException(Throwable exception){
//                String desc = exception.getMessage();
//                SimpleExceptionDialog.INSTANCE.showDialog("Error while loading taclets:", desc, exception); 
//            }
//
//            @Override
//            public void actionPerformed(ActionEvent e) {
//                try {
//                    loadTaclets();        
//                } catch(Throwable exception) {
//                      handleException(exception);  
//                }
//            }
//
//}