/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.LoopInvariant;


/**
 *
 * @author christoph
 */
public class POSnippetFactory {

    public static BasicPOSnippetFactory getBasicFactory(
            FunctionalOperationContract contract,
            ProofObligationVars vars,
            Services services) {
        return new BasicPOSnippetFactoryImpl(contract, vars, services);
    }
    
    public static BasicPOSnippetFactory getBasicFactory(
            LoopInvariant invariant,
            ProofObligationVars vars,
            Services services) {
        return new BasicPOSnippetFactoryImpl(invariant, vars, services);
    }


    public static BasicPOSnippetFactory getBasicFactory(
            InformationFlowContract contract,
            ProofObligationVars vars,
            Services services) {
        return new BasicPOSnippetFactoryImpl(contract, vars, services);
    }


    static BasicPOSnippetFactory getBasicFactory(
            BasicSnippetData data,
            ProofObligationVars poVars) {
        return new BasicPOSnippetFactoryImpl(data, poVars);
    }


    public static InfFlowPOSnippetFactory getInfFlowFactory(
            InformationFlowContract contract,
            ProofObligationVars vars1,
            ProofObligationVars vars2,
            Services services) {
        return new InfFlowPOSnippetFactoryImpl(contract, vars1, vars2, services);
    }
    
    public static InfFlowPOSnippetFactory getInfFlowFactory(
            LoopInvariant invariant,
            ProofObligationVars vars1,
            ProofObligationVars vars2,
            Services services) {
        return new InfFlowPOSnippetFactoryImpl(invariant, vars1, vars2, services);
    }

    static InfFlowPOSnippetFactory getInfFlowFactory(
            BasicSnippetData data,
            ProofObligationVars vars1,
            ProofObligationVars vars2) {
        return new InfFlowPOSnippetFactoryImpl(data, vars1, vars2);
    }
}
