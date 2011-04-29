package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Vector;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.LoaderListener;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.TacletInfo;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;
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
    
    public void start() throws IOException{
	println("Start problem creation:");
	println(options.toString());
	ProblemInitializer pi = createProblemInitializer();
	File file = new File(options.getPathOfRuleFile());
	LoaderListener loaderListener = new LoaderListener() {
	    
	    @Override
	    public void stopped(Throwable exception) {
		handleException(exception);
	    }
	    
	    @Override
	    public void stopped(ProofAggregate pa, ImmutableSet<Taclet> taclets) {
		if(pa == null){
		    println("There is no taclet to be proven.");
		    return;
		}
		println("Proofs have been created for");
		if(options.getPrintStream() != null){
		    for(Proof p : pa.getProofs()){
			println(p.name().toString());
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
		file ,createDummyKeYFile(), loaderListener, pi,this );
	loader.start();	
    }
    
    private File createDummyKeYFile() throws IOException{
	File file = new File(options.getHomePath()+File.separator+"lemmataGenDummy.key");
	file.deleteOnExit();
	String s = "\\problem{true}";
	FileWriter writer = new FileWriter(file);
	writer.write(s);
	writer.close();
	return file;	
    }
    
    private void handleException(Throwable exception){
	printException(exception);
    }
    
    private void startProofs(ProofAggregate pa){
	println("Start the proving:");
	for(Proof p : pa.getProofs()){
	    try{
		startProof(p);
		if(options.isSavingResultsToFile()){
		    saveProof(p);
		}
	    }catch(Throwable e){
		handleException(e);
	    }
	}
    }
    
    private void saveProof(Proof p) throws IOException{
	   ProofSaver saver = new ProofSaver(p,options.createProofPath(p), 
	   options.getInternalVersion());
	   saver.save();
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
    public ImmutableSet<Taclet> filter(Vector<TacletInfo> taclets) {
	ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
	for(TacletInfo tacletInfo : taclets){
	    if(!tacletInfo.isAlreadyInUse()){
		set = set.add(tacletInfo.getTaclet());
	    }
	}
	
	return set;
    }

    

}
