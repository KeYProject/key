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

package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;
import de.uka.ilkd.key.taclettranslation.lemma.TacletLoader;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.LoaderListener;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletInfo;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

public class LemmataHandler implements TacletFilter {
        private final LemmataAutoModeOptions options;
        private final Profile profile;

        public LemmataHandler(LemmataAutoModeOptions options, Profile profile) {
                this.options = options;
                this.profile = profile;
        }

        public void println(String s) {
                if (options.getPrintStream() != null) {
                        options.getPrintStream().println(s);
                }
        }

        public void print(String s) {
                if (options.getPrintStream() != null) {
                        options.getPrintStream().print(s);
                }
        }

        public void printException(Throwable t) {
                if (options.getPrintStream() != null) {
                        t.printStackTrace(options.getPrintStream());
                }
        }

        public void start() throws IOException, ProofInputException {
                println("Start problem creation:");
                println(options.toString());

                File file = new File(options.getPathOfRuleFile());
                File fileForDefinitions =  options.getPathOfRuleFile() != "" ? new File(options.getPathOfDefinitionFile()) :file;
                Collection<File> filesForAxioms = createFilesForAxioms(options.getFilesForAxioms());
                
                final ProblemInitializer problemInitializer = new ProblemInitializer(null,
                                profile, new Services(
                                                new KeYRecoderExcHandler()),
                                false, new Listener());
                
                TacletLoader tacletLoader = new TacletLoader.TacletFromFileLoader(null,
                                                      new Listener(),
                                                      problemInitializer,
                                                      profile,
                                                      fileForDefinitions ,
                                                      file,
                                                      filesForAxioms,
                                                      null);
                
                
                LoaderListener loaderListener = new LoaderListener() {

                        @Override
                        public void stopped(Throwable exception) {
                                handleException(exception);
                        }

                        @Override
                        public void stopped(ProofAggregate pa,
                                        ImmutableSet<Taclet> taclets,boolean addAsAxioms) {
                                if (pa == null) {
                                        println("There is no taclet to be proven.");
                                        return;
                                }
                                println("Proofs have been created for");
                                if (options.getPrintStream() != null) {
                                        for (Proof p : pa.getProofs()) {
                                                println(p.name().toString());
                                        }
                                }
                                startProofs(pa);

                        }

                        @Override
                        public void started() {
                                println("Start loading the problem");
                        }

                        @Override
                        public void progressStarted(Object sender) {
                
                                
                        }

                        @Override
                        public void reportStatus(Object sender, String string) {
                  
                                
                        }

                        @Override
                        public void resetStatus(Object sender) {
                  
                                
                        }
                };
      
                TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(loaderListener,this,true,tacletLoader);
                
                loader.start();
        }
        
        private Collection<File> createFilesForAxioms(Collection<String> filenames){
                Collection<File> list = new LinkedList<File>();
                for(String filename : filenames){
                    list.add(new File(filename));    
                }
                return list;
        }



        private void handleException(Throwable exception) {
                printException(exception);
        }

        private void startProofs(ProofAggregate pa) {
                println("Start the proving:");
                for (Proof p : pa.getProofs()) {
                        try {
                                startProof(p);
                                if (options.isSavingResultsToFile()) {
                                        saveProof(p);
                                }
                        } catch (Throwable e) {
                                handleException(e);
                        }
                }
        }

        private void saveProof(Proof p) throws IOException {
                ProofSaver saver = new ProofSaver(p,
                                options.createProofPath(p),
                                options.getInternalVersion());
                saver.save();
        }

        private void startProof(Proof proof) {
                print(proof.name() + "...");
                AutomaticProver prover = new AutomaticProver();
                try {
                        prover.start(proof, options.getMaxNumberOfRules(),
                                        options.getTimeout());
                        println(proof.closed() ? "closed" : ("not closed (open goals: "+proof.openGoals().size()
                                        +" nodes: "+proof.countNodes()+")"));
                } catch (InterruptedException exception) {
                        println("time out");
                }

        }

        private class Listener implements ProblemInitializerListener {

                @Override
                public void proofCreated(ProblemInitializer sender,
                                ProofAggregate proofAggregate) {
                        println("The proofs have been initialized.");
                }

                @Override
                public void progressStarted(Object sender) {
            
                }

                @Override
                public void progressStopped(Object sender) {
        
                }

                @Override
                public void reportStatus(Object sender, String status,
                                int progress) {
                        println("Status: " + status);
                }

                @Override
                public void reportStatus(Object sender, String status) {
                        println("Status: " + status);
                }

                @Override
                public void resetStatus(Object sender) {

                }

                @Override
                public void reportException(Object sender, ProofOblInput input,
                                Exception e) {
                        printException(e);
                }

        }

        @Override
        public ImmutableSet<Taclet> filter(List<TacletInfo> taclets) {
                ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
                for (TacletInfo tacletInfo : taclets) {
                        if (!tacletInfo.isAlreadyInUse()
                                        && !tacletInfo.isNotSupported()) {
                                set = set.add(tacletInfo.getTaclet());
                        }
                }

                return set;
        }

}