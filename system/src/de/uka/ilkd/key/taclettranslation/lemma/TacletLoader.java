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
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.lemmatagenerator.EnvironmentCreator;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import de.uka.ilkd.key.util.ProgressMonitor;

public abstract class TacletLoader {
        
        public abstract ImmutableSet<Taclet> loadAxioms();
        public abstract ImmutableSet<Taclet> loadTaclets();
        public abstract ImmutableSet<Taclet> getTacletsAlreadyInUse();
        
        protected KeYUserProblemFile tacletFile;
        protected final ProgressMonitor monitor;
        protected final ProblemInitializerListener listener;
        protected final Profile    profile;
        protected ProofEnvironment envForTaclets;
  
        public TacletLoader(ProgressMonitor monitor,
                        ProblemInitializerListener listener,
                        Profile profile) {
                super();
                this.monitor = monitor;
                this.listener = listener;
                this.profile = profile;
        }
        
    
        public KeYUserProblemFile getTacletFile() {
                return tacletFile;
        }


        public ProofEnvironment getProofEnvForTaclets() {
                if(envForTaclets == null){
                        try{
                                EnvironmentCreator ec = new EnvironmentCreator();
                        envForTaclets =  ec.create(PathConfig.getKeyConfigDir(), monitor, listener, profile); 
                          if(tacletFile == null){
                                  tacletFile = ec.getKeyFile();
                                           
                          }
                        }catch(Throwable e){
                                throw new RuntimeException(e);
                        }
                 }
                return envForTaclets;
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
               
               public TacletFromFileLoader(TacletFromFileLoader loader, InitConfig initConfig){
                       super(loader.monitor,loader.listener, loader.profile);
                       assert initConfig == null || loader.profile == initConfig.getProfile();
                       this.problemInitializer = loader.problemInitializer;
                       this.fileForDefinitions = loader.fileForDefinitions;
                       this.fileForTaclets = loader.fileForTaclets;
                       this.filesForAxioms = loader.filesForAxioms;
                       this.envForTaclets = loader.envForTaclets;
                       this.initConfig = initConfig;
               }
 

                public void prepare() {
                        KeYUserProblemFile keyFileDefs = new KeYUserProblemFile(
                                        "Definitions", fileForDefinitions, 
                                        monitor, initConfig.getProfile());
                        try {
                                initConfig = problemInitializer.prepare(keyFileDefs);
                        } catch (ProofInputException e) {
                                throw new RuntimeException(e);
                        }
                }
                

       

                @Override
                public ImmutableSet<Taclet> loadTaclets() {
                        if(initConfig == null){
                                prepare();
                        }
                        tacletFile = new KeYUserProblemFile(
                                        fileForTaclets.getName(), fileForTaclets, monitor, initConfig.getProfile());
                        return load(tacletFile, initConfig);
                        
                }
                
                @Override
                public ImmutableSet<Taclet> loadAxioms()
                                 {
                        if(initConfig == null){
                                prepare();
                        }
                        ImmutableSet<Taclet> axioms = DefaultImmutableSet.nil();
                        for (File f : filesForAxioms) {
                                KeYUserProblemFile keyFile = new KeYUserProblemFile(
                                                f.getName(), f, monitor, initConfig.getProfile());
                                ImmutableSet<Taclet> taclets = load(keyFile, initConfig);
                                getProofEnvForTaclets().registerRules(taclets,
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

                
                private ImmutableSet<Taclet> load(KeYUserProblemFile keyFile,
                                InitConfig reference) 
                                {
                        
                        // this ensures that necessary Java types are loaded
                        InitConfig config = createInitConfig(reference);

                        keyFile.setInitConfig(config);
                        try{
                            keyFile.readRulesAndProblem();
                        }catch(Throwable e){
                                throw new RuntimeException(e);
                        }
                        return config.getTaclets();
                }




                @Override
                public KeYUserProblemFile getTacletFile() {
                       return tacletFile;
                }



                @Override
                public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
                        return getProofEnvForTaclets().getInitConfig().getTaclets();
                }        
        }
        
        public static class KeYsTacletsLoader extends TacletLoader{


                
                

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
                                getProofEnvForTaclets().registerRules( getProofEnvForTaclets().getInitConfig().getTaclets(), AxiomJustification.INSTANCE);                                    
                             return getProofEnvForTaclets().getInitConfig().getTaclets();             
                        } catch (Throwable e) {
                                throw new RuntimeException(e);
                        }
                        
                }
                



                @Override
                public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
                        return DefaultImmutableSet.nil();
                }
                
        }
        


}