package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.proof.Proof;

public class OracleGenerator {
	
	Proof proof;
	ProofInfo info;
	public OracleGenerator(Proof proof) {
		this.proof = proof;
		info = new ProofInfo(proof);
	}
	
	
	
	
	
	
}
