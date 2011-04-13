package de.uka.ilkd.key.taclettranslation.lemma;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletFormula;

public class ProofObligationCreator {
    
    static public ProofAggregate create(ImmutableSet<Taclet> taclets, InitConfig initConfig){
	
	ProofAggregate[] singleProofs = new ProofAggregate[taclets.size()];
	int i=0; 
	for(Taclet taclet : taclets){
	    singleProofs[i] = create(taclet, initConfig);
	    i++;
	}
	
	ProofAggregate proofAggregate = singleProofs.length==1 ? 
		 singleProofs[0] : ProofAggregate.createProofAggregate(singleProofs, "TEST");

        return proofAggregate;
    }
    
    
    static private ProofAggregate create(Taclet taclet, InitConfig initConfig){
	LemmaGenerator generator = new DefaultLemmaGenerator();
	TacletFormula formula = generator.translate(taclet, initConfig.getServices());
	String name = taclet.name().toString();
	return ProofAggregate.createProofAggregate(new Proof(name,
                formula.getFormula(),
                "NOT YET IMPLEMENTED",
                initConfig.createTacletIndex(),
                initConfig.createBuiltInRuleIndex(),
                initConfig.getServices()),
                name);
    }
    

    
    
}
