/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.InformationFlowContract;


/**
 *
 * @author christoph
 */
public interface InfFlowRelatedPO {
    public InformationFlowContract getContract();

    public InfFlowProofSymbols getIFSymbols();

    public void addIFSymbol(Term t);

    public void addIFSymbol(Named n);

    public void addLabeledIFSymbol(Term t);

    public void addLabeledIFSymbol(Named n);

    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols);
}