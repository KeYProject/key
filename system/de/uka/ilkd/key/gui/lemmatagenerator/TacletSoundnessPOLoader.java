package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.util.LinkedList;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.ProofObligationCreator;
import de.uka.ilkd.key.taclettranslation.lemma.TacletLoader;
import de.uka.ilkd.key.util.ProgressMonitor;

public class TacletSoundnessPOLoader {
    private final ProgressMonitor progressMonitor;
    private final File    file;
    private final ProofEnvironment env;
    private LinkedList<LoaderListener> listeners = new LinkedList<LoaderListener>();
    private ProofAggregate  resultingProof;
    private ImmutableSet<Taclet> resultingTaclets = DefaultImmutableSet.nil();
    
    static public interface LoaderListener{
	public void started();
	public void stopped(ProofAggregate p,  ImmutableSet<Taclet> taclets);
	public void stopped(Throwable exception); 
    }  
    
    
    public TacletSoundnessPOLoader(
            ProgressMonitor progressMonitor, File file,
            ProofEnvironment env, LoaderListener listener) {
	this(progressMonitor, file, env);
	listeners.add(listener);
    }
    
    public TacletSoundnessPOLoader(
            ProgressMonitor progressMonitor, File file,
            ProofEnvironment env) {
	super();
	this.progressMonitor = progressMonitor;
	this.file = file;
	this.env = env;
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
	ImmutableSet<Taclet> taclets = 
	    tacletLoader.load(keyFile, env.getInitConfig());


	// let the user select specific taclets.
	LemmaSelectionDialog dialog = new LemmaSelectionDialog();
	resultingTaclets = dialog.showModal(taclets);

	

	ProofAggregate p = ProofObligationCreator.create(getResultingTaclets(), env.getInitConfig());

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


