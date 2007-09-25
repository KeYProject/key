package de.uka.ilkd.key.proof;

public class SingleProof extends ProofAggregate {

    private Proof proof;
    
    public SingleProof(Proof p, String name) {
        super(name);
        this.proof = p;
    }
    
    public void updateProofStatus() {
        proof.mgt().updateProofStatus();
        proofStatus = proof.mgt().getStatus();
    }

    public Proof[] getProofs() {
        return new Proof[]{proof};
    }
    
    public int size() {
        return 1;
    }
    
    public ProofAggregate[] getChildren() {
        return new ProofAggregate[0];
    }
}
