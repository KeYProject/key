package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.HashMap;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletBuilder;



public class TacletLoader {
    public static TacletLoader INSTANCE = new TacletLoader();
    private InitConfig createInitConfig(InitConfig reference){
	  InitConfig newConfig =  reference.copy();
	
	  
	  newConfig.setTaclets ( DefaultImmutableSet.<Taclet>nil() );
	  newConfig.setTaclet2Builder ( new HashMap<Taclet, TacletBuilder> () );
	
          return newConfig;
    }
    
    public ImmutableSet<Taclet> load(KeYUserProblemFile keyFile,InitConfig reference)
    throws ProofInputException{
	// this ensures that necessary Java types are loaded
	InitConfig config = createInitConfig(reference);
	
	
	
	keyFile.setInitConfig(config);
	keyFile.readRulesAndProblem();
	

	/*keyFile.readIncludes();
	keyFile.readJavaPath();
	keyFile.readSorts();
	keyFile.readRulesAndProblem();	*/
	return config.getTaclets();
    }
    


    
    
}
