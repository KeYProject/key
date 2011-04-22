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
    private final Listener listener = new Listener();
    
    public LemmataHandler(LemmataAutoModeOptions options, Profile profile){
	this.options = options;
	this.profile = profile;
	
    }
    
    public void loadLemata(){
       
    }
    
    private void loadProblem(){
	
    }
    
    public void proveLemata(){
	
    }
    
    
    
    public void start(){
	System.out.println("START");
	ProblemInitializer pi = createProblemInitializer();
	File file = new File(options.getPathOfRuleFile());
	LoaderListener loaderListener = new LoaderListener() {
	    
	    @Override
	    public void stopped(Throwable exception) {
		// TODO Auto-generated method stub
		
	    }
	    
	    @Override
	    public void stopped(ProofAggregate pa, ImmutableSet<Taclet> taclets) {
		System.out.println("Proof created");
		
		for(Proof p : pa.getProofs()){
		    System.out.println(p);
		}
		startProofs(pa);
	
		
	    }
	    
	    @Override
	    public void started() {
		// TODO Auto-generated method stub
		
	    }
	};
	TacletSoundnessPOLoader loader = new TacletSoundnessPOLoader(null,
		file , loaderListener, pi,this );
	loader.start();	
    }
    
    private void startProofs(ProofAggregate pa){
	for(Proof p : pa.getProofs()){
	    startProof(p);
	}
    }
    
    private void startProof(Proof proof){
	System.out.println("Proof: " + proof.name());
        AutomaticProver prover = new AutomaticProver();
        try{
        prover.start(proof, options.getMaxNumberOfRules(),options.getTimeout());
        }catch(InterruptedException exception){
            System.out.println("Proof has been interrupted: Timeout");
        }
	System.out.println("Closed" + proof.closed());
    }
    
    
    private ProblemInitializer createProblemInitializer(){
	return new ProblemInitializer(null,profile , new Services(new KeYRecoderExcHandler()), 
		false,new Listener()); 
    }
    
    private static class Listener implements ProblemInitializerListener
                {

	@Override
        public void proofCreated(ProblemInitializer sender,
                ProofAggregate proofAggregate) {
	    System.out.println("Proof created");
        }

	@Override
        public void progressStarted(Object sender) {
	    System.out.println("Progress started");
        }

	@Override
        public void progressStopped(Object sender) {
	    System.out.println("Progress stopped");
        }

	@Override
        public void reportStatus(Object sender, String status, int progress) {
	    System.out.println("Status: " + status);
        }

	@Override
        public void reportStatus(Object sender, String status) {
	    System.out.println("Status: " + status );
        }

	@Override
        public void resetStatus(Object sender) {

        }

	@Override
        public void reportException(Object sender, ProofOblInput input,
                Exception e) {
	    System.out.println("ERROR:");
	    System.out.println(e.getMessage());
        }	
	
    }

    @Override
    public ImmutableSet<Taclet> filter(ImmutableSet<Taclet> taclets) {
	for(Taclet taclet : taclets){
	    System.out.println("Taclet: " + taclet.displayName());
	}
	return taclets;
    }

    

}
