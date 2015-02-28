package de.uka.ilkd.key.informationflow.po;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;

public interface InfFlowPO {

    public IFProofObligationVars getLeaveIFVars();

    public InfFlowProofSymbols getIFSymbols();

    public void addIFSymbol(Term t);

    public void addIFSymbol(Named n);

    public void addLabeledIFSymbol(Term t);

    public void addLabeledIFSymbol(Named n);

    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols);
    
}
