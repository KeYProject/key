package de.uka.ilkd.key.taclettranslation;

import java.io.File;
import java.io.FileWriter;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;
import java.util.Vector;

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
    private final File    dummyFile;
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
	public ImmutableSet<Taclet> filter(Vector<TacletInfo> taclets);
    }
    
    static public class TacletInfo{
	private Taclet taclet;
	private boolean alreadyInUse;
	public Taclet getTaclet() {
            return taclet;
        }
	public boolean isAlreadyInUse() {
            return alreadyInUse;
        }
	public TacletInfo(Taclet taclet, boolean alreadyInUse) {
	    super();
	    this.taclet = taclet;
	    this.alreadyInUse = alreadyInUse;
        }
	
    }
    
    
    public TacletSoundnessPOLoader(
            ProgressMonitor progressMonitor, File file, File dummyFile,
            ProofEnvironment env, LoaderListener listener,TacletFilter filter) {
	this(progressMonitor, file,dummyFile, env,filter);
	if(listener != null){
	    listeners.add(listener);
	}
    }
    
    private TacletSoundnessPOLoader(
            ProgressMonitor progressMonitor, File file,File dummyFile,
            ProofEnvironment referenceEnv,TacletFilter filter) {
	super();
	this.progressMonitor = progressMonitor;
	this.file = file;
	this.env = referenceEnv;
	this.tacletFilter = filter;
	this.dummyFile = dummyFile;
    }
    
    public TacletSoundnessPOLoader(
            ProgressMonitor progressMonitor, File file,File dummyFile,
            LoaderListener listener,ProblemInitializer problemInitializer,
            TacletFilter filter) {
	this(progressMonitor, file,dummyFile, null,listener,filter);
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
   
    private Vector<TacletInfo> createTacletInfo(ImmutableSet<Taclet> taclets, ImmutableSet<Taclet> base){
	Vector<TacletInfo> collectionOfTacletInfo = new Vector<TacletInfo>();
	TreeSet<Taclet> treeSet = new TreeSet<Taclet>(new Comparator<Taclet>() {
	    @Override
            public int compare(Taclet o1, Taclet o2) {
	        return o1.name().toString().compareTo(o2.name().toString());
            }
	});
	for(Taclet taclet : base){
	    treeSet.add(taclet);
	}
	
	for(Taclet taclet : taclets){
		collectionOfTacletInfo.add(new TacletInfo(taclet,treeSet.contains(taclet)));
	}
	return collectionOfTacletInfo;
    }
    

    
    private void doWork() throws ProofInputException{
	TacletLoader tacletLoader = new TacletLoader();
	
	

	
	KeYUserProblemFile keyFile = new KeYUserProblemFile(file.getName(), file, progressMonitor);
	InitConfig initConfig;
	if(env == null){
	    KeYUserProblemFile dummyKeYFile = new KeYUserProblemFile(dummyFile.getName(), dummyFile, progressMonitor);
	    initConfig = problemInitialzer.prepare(dummyKeYFile);
	    env = new ProofEnvironment(initConfig); 
	}
	initConfig = env.getInitConfig(); 



	ImmutableSet<Taclet> taclets = 
	    tacletLoader.load(keyFile, initConfig);

	
	Vector<TacletInfo> collectionOfTacletInfo = createTacletInfo(taclets,
		initConfig.getTaclets());

	resultingTaclets = tacletFilter.filter(collectionOfTacletInfo);
	
	if(getResultingTaclets().isEmpty()){
	    return;
	}
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


