package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.util.LinkedList;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.ProofObligationCreator;
import de.uka.ilkd.key.taclettranslation.lemma.TacletLoader;
import de.uka.ilkd.key.util.ProgressMonitor;

public class TacletSoundnessPOLoader {
    private final ProgressMonitor progressMonitor;
    private final File    file;
    private ProofEnvironment env;
    private LinkedList<LoaderListener> listeners = new LinkedList<LoaderListener>();
    private ProofAggregate  resultingProof;
    private ImmutableSet<Taclet> resultingTaclets = DefaultImmutableSet.nil();
    private ProblemInitializer problemInitialzer; 
    private TacletFilter tacletFilter;
    
    static public interface LoaderListener{
	public void started();
	public void stopped(ProofAggregate p,  ImmutableSet<Taclet> taclets);
	public void stopped(Throwable exception); 
    }  
    
    static public interface TacletFilter{
	public ImmutableSet<Taclet> filter(ImmutableSet<Taclet> taclets);
    }
    
    
    public TacletSoundnessPOLoader(
            ProgressMonitor progressMonitor, File file,
            ProofEnvironment env, LoaderListener listener,TacletFilter filter) {
	this(progressMonitor, file, env,filter);
	if(listener != null){
	    listeners.add(listener);
	}
    }
    
    public TacletSoundnessPOLoader(
            ProgressMonitor progressMonitor, File file,
            ProofEnvironment referenceEnv,TacletFilter filter) {
	super();
	this.progressMonitor = progressMonitor;
	this.file = file;
	this.env = referenceEnv;
	this.tacletFilter = filter;
    }
    
    public TacletSoundnessPOLoader(
            ProgressMonitor progressMonitor, File file,
            LoaderListener listener,ProblemInitializer problemInitializer,
            TacletFilter filter) {
	this(progressMonitor, file, null,listener,filter);
	this.problemInitialzer = problemInitializer;
    }
    
    
    public void addListener(LoaderListener listener){
	listeners.add(listener);
    }
    
    public void removeListener(LoaderListener listener){
	listeners.remove(listener);
    }
    

    public void start(){
	for(LoaderListener listener : listeners){
	    listener.started();
	}
	Thread thread = new Thread(new Working());
	thread.start();
    }
    
       
   private class Working implements Runnable{
	@Override
	public void run() {
	   try{
	       doWork();
	   }catch(final Throwable exception){
	       SwingUtilities.invokeLater(new Runnable() {
	        @Override
	        public void run() {
		    for(LoaderListener listener : listeners){
			    listener.stopped(exception);
		    } 
	        }
	    });
	   }	   
	   finally{
	       SwingUtilities.invokeLater(new Runnable() {
		        @Override
		        public void run() {
		            
			    for(LoaderListener listener : listeners){
				    listener.stopped(resultingProof,getResultingTaclets());
			    } 
		        }
		    });
	   }	    
	}	
    }
    
    private void doWork() throws ProofInputException{
	TacletLoader tacletLoader = new TacletLoader();
	KeYUserProblemFile keyFile = new KeYUserProblemFile(file.getName(), file, progressMonitor);
	InitConfig initConfig;
	if(env == null){
	    initConfig = problemInitialzer.prepare(keyFile);
	    env = new ProofEnvironment(initConfig); 
	}
	initConfig = env.getInitConfig(); 
	
	ImmutableSet<Taclet> taclets = 
	    tacletLoader.load(keyFile, initConfig);


	resultingTaclets = tacletFilter.filter(taclets);
	

	ProofAggregate p = ProofObligationCreator.create(getResultingTaclets(), initConfig);
        
	env.registerProof(keyFile,p);
	resultingProof = p;
    }
    
    public ProofAggregate getResultingProof() {
	return resultingProof;
    }
    public ImmutableSet<Taclet> getResultingTaclets() {
	return resultingTaclets;
    }
  

}


