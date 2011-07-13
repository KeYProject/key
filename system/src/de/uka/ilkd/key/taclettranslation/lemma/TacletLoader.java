package de.uka.ilkd.key.taclettranslation.lemma;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;


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
import de.uka.ilkd.key.rule.TacletBuilder;
import de.uka.ilkd.key.util.ProgressMonitor;

public interface TacletLoader {
        
        public ImmutableSet<Taclet> loadAxioms();
        public ImmutableSet<Taclet> loadTaclets();
        public KeYUserProblemFile   getTacletFile();
        public ProofEnvironment     getProofEnvForTaclets();
        public ImmutableSet<Taclet> getTacletsAlreadyInUse();
  
        
        public class TacletFromFileLoader implements TacletLoader{
                private final ProgressMonitor  pm;
                private final ProblemInitializer pi;
                private InitConfig initConfig;
                private KeYUserProblemFile  tacletFile;
                private final ProofEnvironment envForTaclets;
                
                private final File fileForDefinitions;
                private final File fileForTaclets;
                private final Collection<File> filesForAxioms;
       
                
           
           
               public TacletFromFileLoader(ProgressMonitor pm,
                                ProblemInitializer pi,
                                ProofEnvironment envForTaclets,
                                File fileForDefinitions, File fileForTaclets,
                                Collection<File> filesForAxioms) {
                        super();
                        this.pm = pm;
                        this.pi = pi;
                        this.envForTaclets = envForTaclets;
                        this.fileForDefinitions = fileForDefinitions;
                        this.fileForTaclets = fileForTaclets;
                        this.filesForAxioms = filesForAxioms;
                        
                }




                public void prepare() {
                        KeYUserProblemFile keyFileDefs = new KeYUserProblemFile(
                                        "Definitions", fileForDefinitions,
                                        pm);
                        try {
                                initConfig = pi.prepare(keyFileDefs);
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
                                        fileForTaclets.getName(), fileForTaclets, pm);
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
                                                f.getName(), f, pm);
                                ImmutableSet<Taclet> taclets = load(keyFile, initConfig);
                                envForTaclets.registerRules(taclets,
                                                AxiomJustification.INSTANCE);
                                axioms = axioms.union(taclets);
                        }

                        return axioms;
                }  
                
               
                private InitConfig createInitConfig(InitConfig reference) {
                        InitConfig newConfig = reference.copy();

                        newConfig.setTaclets(DefaultImmutableSet.<Taclet> nil());
                        newConfig.setTaclet2Builder(new HashMap<Taclet, TacletBuilder>());
                       
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
                public ProofEnvironment getProofEnvForTaclets() {
                        return envForTaclets;
                }




                @Override
                public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
                        return envForTaclets.getInitConfig().getTaclets();
                }        
        }
        
        public class KeYsTacletsLoader implements TacletLoader{

                private KeYUserProblemFile tacletFile;
                private final ProgressMonitor monitor;
                private final ProblemInitializerListener listener;
                private final Profile    profile;
                private ProofEnvironment envForTaclets;
                
                
                
                public KeYsTacletsLoader(ProgressMonitor monitor,
                                ProblemInitializerListener listener,
                                Profile profile) {
                        super();
                        this.monitor = monitor;
                        this.listener = listener;
                        this.profile = profile;
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
                public KeYUserProblemFile getTacletFile() {
                        return tacletFile;
                }

                @Override
                public ProofEnvironment getProofEnvForTaclets() {
                        if(envForTaclets == null){
                                try{
                                envForTaclets =  EnvironmentCreator.create(PathConfig.KEY_CONFIG_DIR, monitor, listener, profile); 
                                
                                }catch(Throwable e){
                                        throw new RuntimeException(e);
                                }
                         }
                        return envForTaclets;
                }

                @Override
                public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
                        return DefaultImmutableSet.nil();
                }
                
        }
        


}
