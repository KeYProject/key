package de.uka.ilkd.key.informationflow.po;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofOblInput;

public interface InfFlowPO extends ProofOblInput {

    /**
     * Get the information flow proof obligation variables (set of four sets of
     * proof obligation variables necessary for information flow proofs) for
     * the "leaf" (i.e., child of child of ..) information flow proof
     * obligation.
     * @return the information flow proof obligation variables.
     */
    public IFProofObligationVars getLeafIFVars();

    public InfFlowProofSymbols getIFSymbols();

    public void addIFSymbol(Term t);

    public void addIFSymbol(Named n);

    public void addLabeledIFSymbol(Term t);

    public void addLabeledIFSymbol(Named n);

    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols);
    
}
