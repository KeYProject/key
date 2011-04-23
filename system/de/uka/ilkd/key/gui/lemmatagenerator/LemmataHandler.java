package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.util.EventObject;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.InteractiveProver;
import de.uka.ilkd.key.gui.lemmatagenerator.TacletSoundnessPOLoader.LoaderListener;
import de.uka.ilkd.key.gui.lemmatagenerator.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

public class LemmataHandler implements TacletFilter{
    private final LemmataAutoModeOptions options;
    private final Profile profile;
    
    public LemmataHandler(LemmataAutoModeOptions options, Profile profile){
	this.options = options;
	this.profile = profile;
    }
    
 
    public void println(String s){
	if(options.getPrintStream()!=null){
	    options.getPrintStream().println(s);
	}
    }
    
    public void print(String s){
	if(options.getPrintStream()!=null){
	    options.getPrintStream().print(s);
	}
    }
    
    public void printException(Throwable t){
	if(options.getPrintStream() !=null){
	    t.printStackTrace(options.getPrintStream());
	}
    }
    
    public void start(){
	println("Start problem creation:");
	ProblemInitializer pi = createProblemInitializer();
	File file = new File(options.getPathOfRuleFile());
	LoaderListener loaderListener = new LoaderListener() {
	    
	    @Override
	    public void stopped(Throwable exception) {
		printException(exception);
	    }
	    
	    @Override
	    public void stopped(ProofAggregate pa, ImmutableSet<Taclet> taclets) {
		println("Proofs have been created for");
		if(options.getPrintStream() != null){
		    for(Proof p : pa.getProofs()){
			println("Taclet: "+p.name());
		    }		
		}
		startProofs(pa);
	    }
	    
	    @Override
	    public void started() {
		println("Start loading the problem");
	    }
	};
	TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(null,
		file , loaderListener, pi,this );
	loader.start();	
    }
    
    private void startProofs(ProofAggregate pa){
	println("Start the proving:");
	for(Proof p : pa.getProofs()){
	    startProof(p);
	}
    }
    
    private void startProof(Proof proof){
	print(proof.name()+"...");
        AutomaticProver prover = new AutomaticProver();
        try{
            prover.start(proof, options.getMaxNumberOfRules(),options.getTimeout());
            println(proof.closed()?"closed":"not closed");
        }catch(InterruptedException exception){
           println("time out");
        }
	
    }
    
    
    private ProblemInitializer createProblemInitializer(){
	return new ProblemInitializer(null,profile , new Services(new KeYRecoderExcHandler()), 
		false,new Listener()); 
    }
    
    private class Listener implements ProblemInitializerListener
                {

	@Override
        public void proofCreated(ProblemInitializer sender,
                ProofAggregate proofAggregate) {
	    println("The proofs have been initialized.");
        }

	@Override
        public void progressStarted(Object sender) {
	    println("Process of initializing the proofs has been started.");
        }

	@Override
        public void progressStopped(Object sender) {
	    println("Process of initializing the proofs has been stopped.");
        }

	@Override
        public void reportStatus(Object sender, String status, int progress) {
	   println("Status: "+status);
        }

	@Override
        public void reportStatus(Object sender, String status) {
	   println("Status: " + status );
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
    public ImmutableSet<Taclet> filter(ImmutableSet<Taclet> taclets) {
	
	return taclets;
    }

    

}
