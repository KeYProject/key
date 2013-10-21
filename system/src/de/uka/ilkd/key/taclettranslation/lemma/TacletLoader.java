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

package de.uka.ilkd.key.taclettranslation.lemma;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.lemmatagenerator.EnvironmentCreator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import de.uka.ilkd.key.util.ProgressMonitor;

public abstract class TacletLoader {

    protected KeYUserProblemFile tacletFile;
    protected final ProgressMonitor monitor;
    protected final ProblemInitializerListener listener;
    protected final Profile profile;
    protected ProofEnvironment envForTaclets;

    public TacletLoader(ProgressMonitor monitor,
            ProblemInitializerListener listener,
            Profile profile) {
        super();
        this.monitor = monitor;
        this.listener = listener;
        this.profile = profile;
    }

    /** 
     * get the set of axioms from the axiom files if applicable.
     */
    public abstract ImmutableSet<Taclet> loadAxioms();

    /** 
     * get the set of taclets to examine
     * (either from the system or from a file)
     */
    public abstract ImmutableSet<Taclet> loadTaclets();

    /**
     * get the taclet base which is considered fix (?) 
     */
    public abstract ImmutableSet<Taclet> getTacletsAlreadyInUse();

    /**
     * subclasses give a special proof obligation input per proof.
     * They can choose the implementing class and pass to it any
     * necessary information.
     */
    public abstract ProofOblInput getTacletFile(Proof proof);

    /**
     * When proving existing system taclets, all rules which occurred prior to the 
     * desired taclet need to be elminated from the set of available taclets to
     * avoid circular proofs.
     * 
     * This method removes all taclets in initConfig's taclet database from the
     * first taclet that is also in taclets.
     * 
     * @param taclets
     *            the taclet list for which PO will be generated. Remove all taclets
     *            after the first taclet in the list.
     *
     * @param initConfig the initial config from which the taclet base is taken
     */

    public void manageAvailableTaclets(InitConfig initConfig,
            ImmutableSet<Taclet> tacletsToAdd,
            ImmutableSet<Taclet> tacletsToProve) {
        List<Taclet> sysTaclets = toList(initConfig.getTaclets());
        Collections.reverse(sysTaclets);
        List<Taclet> addedList = toList(tacletsToAdd);
        Collections.reverse(addedList);
        sysTaclets.addAll(addedList);

        ImmutableSet<Taclet> newTaclets = DefaultImmutableSet.nil();
        HashMap<Taclet, TacletBuilder> map = initConfig.getTaclet2Builder();
        boolean tacletfound = false;
        for (Taclet taclet : sysTaclets) {
            if (tacletsToProve.contains(taclet)) {
                tacletfound = true;
            }

            if(!tacletfound) {
                newTaclets = newTaclets.add(taclet);
            } else {
                map.remove(taclet);
            }
        }

        initConfig.setTaclets(newTaclets);

    }

    public ProofEnvironment getProofEnvForTaclets() {
        if(envForTaclets == null) {
            try {
                EnvironmentCreator ec = new EnvironmentCreator();
                envForTaclets =  ec.create(PathConfig.getKeyConfigDir(), monitor, listener, profile); 
                if(tacletFile == null){
                    tacletFile = ec.getKeyFile();
                }
            } catch(Throwable e) {
                throw new RuntimeException(e);
            }
        }
        return envForTaclets;
    }


//    public void setProofEnvForTaclets(ProofEnvironment proofEnv) {
//        this.envForTaclets = proofEnv;
//    }


    /* 
     * turn an immutable set into an array list 
     */
    private static <E> List<E> toList(ImmutableSet<E> set) {
        ArrayList<E> res = new ArrayList<E>();
        for (E element : set) {
            res.add(element);
        }
        return res;
    }

    public static class TacletFromFileLoader extends TacletLoader{
        private InitConfig initConfig;
        private final File fileForDefinitions;
        private final File fileForTaclets;
        private final Collection<File> filesForAxioms;
        private final ProblemInitializer problemInitializer;

        public TacletFromFileLoader(ProgressMonitor pm,
                ProblemInitializerListener listener,
                ProblemInitializer problemInitializer,
                File fileForDefinitions, File fileForTaclets,
                Collection<File> filesForAxioms,
                ProofEnvironment env) {
            super(pm,listener, env.getInitConfig().getProfile());
            this.fileForDefinitions = fileForDefinitions;
            this.fileForTaclets = fileForTaclets;
            this.filesForAxioms = filesForAxioms;
            this.problemInitializer = problemInitializer;
            this.envForTaclets = env;
            this.initConfig = env.getInitConfig();
        }

        public TacletFromFileLoader(ProgressMonitor pm,
                ProblemInitializerListener listener,
                ProblemInitializer problemInitializer,
                Profile profile,
                File fileForDefinitions, File fileForTaclets,
                Collection<File> filesForAxioms) {
            super(pm,listener,profile);
            this.fileForDefinitions = fileForDefinitions;
            this.fileForTaclets = fileForTaclets;
            this.filesForAxioms = filesForAxioms;
            this.problemInitializer = problemInitializer;
        }

        public TacletFromFileLoader(TacletFromFileLoader loader, InitConfig initConfig) {
            super(loader.monitor,loader.listener, loader.profile);
            assert initConfig == null || loader.profile == initConfig.getProfile();
            this.problemInitializer = loader.problemInitializer;
            this.fileForDefinitions = loader.fileForDefinitions;
            this.fileForTaclets = loader.fileForTaclets;
            this.filesForAxioms = loader.filesForAxioms;
            this.envForTaclets = loader.envForTaclets;
            this.initConfig = initConfig;
        }
        


        private void prepareInitConfig() {
            KeYFile keyFileDefs = new KeYFile(
                    "Definitions", fileForDefinitions,
                    monitor, profile);
            try {
                if(initConfig != null) {
                    problemInitializer.readEnvInput(keyFileDefs, initConfig);
                } else {
                    initConfig = problemInitializer.prepare(keyFileDefs);
                }
            } catch (ProofInputException e) {
                throw new RuntimeException(e);
            }
        }

        @Override
        public ImmutableSet<Taclet> loadTaclets() {
            assert initConfig != null;
            tacletFile = new KeYUserProblemFile(
                    fileForTaclets.getName(), fileForTaclets, monitor, initConfig.getProfile());
            return load(tacletFile, initConfig);

        }

        @Override
        public ImmutableSet<Taclet> loadAxioms() {
            prepareInitConfig();
            ImmutableSet<Taclet> axioms = DefaultImmutableSet.nil();
            for (File f : filesForAxioms) {
                KeYUserProblemFile keyFile = new KeYUserProblemFile(f.getName(), f, monitor, initConfig.getProfile());
                ImmutableSet<Taclet> taclets = load(keyFile, initConfig);
                getProofEnvForTaclets().registerRules(taclets,
                        AxiomJustification.INSTANCE);
                initConfig.getProofEnv().registerRules(taclets,
                        AxiomJustification.INSTANCE);
                axioms = axioms.union(taclets);
            }

            return axioms;
        }


        private InitConfig createInitConfig(InitConfig reference) {
            InitConfig newConfig = reference.deepCopy();
            newConfig.setTaclets(DefaultImmutableSet.<Taclet> nil());
            newConfig.setTaclet2Builder(new LinkedHashMap<Taclet, TacletBuilder>());

            return newConfig;
        }


        private ImmutableSet<Taclet> load(KeYUserProblemFile keyFile, InitConfig reference) {

            // this ensures that necessary Java types are loaded
            InitConfig config = createInitConfig(reference);

            keyFile.setInitConfig(config);
            try {
                keyFile.readRulesAndProblem();
            } catch(Throwable e) {
                throw new RuntimeException(e);
            }
            return config.getTaclets();
        }

        @Override
        public ProofOblInput getTacletFile(Proof proof) {
            String name = proof.name().toString();
            assert name.startsWith("Taclet: ") : 
                "This depends (unfortunately) on the name of the proof";
            TacletProofObligationInput result = 
                    new TacletProofObligationInput(name.substring(8), null);
            result.setLoadInfo(fileForTaclets, fileForDefinitions, filesForAxioms);
            return result;
        }

        @Override
        public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
            return getProofEnvForTaclets().getInitConfig().getTaclets();
        }

    }

    public static class KeYsTacletsLoader extends TacletLoader {

        public KeYsTacletsLoader(ProgressMonitor monitor,
                ProblemInitializerListener listener,
                Profile profile) {
            super(monitor, listener, profile);
        }

        @Override
        public ImmutableSet<Taclet> loadAxioms() {
            return DefaultImmutableSet.nil();
        }

        @Override
        public ImmutableSet<Taclet> loadTaclets() {
            try {
                getProofEnvForTaclets().registerRules(
                        getProofEnvForTaclets().getInitConfig().getTaclets(), 
                        AxiomJustification.INSTANCE);
                return getProofEnvForTaclets().getInitConfig().getTaclets();             
            } catch (Throwable e) {
                throw new RuntimeException(e);
            }

        }

        @Override 
        public ProofOblInput getTacletFile(Proof proof) {
            String name = proof.name().toString();
            assert name.startsWith("Taclet: ") : 
                "This depends (unfortunately) on the name of the proof";
            return new TacletProofObligationInput(name.substring(8), null);
        }


        @Override
        public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
            return DefaultImmutableSet.nil();
        }
    }
}
