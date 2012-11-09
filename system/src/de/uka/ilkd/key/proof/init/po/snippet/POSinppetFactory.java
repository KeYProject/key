/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.InformationFlowContract;

/**
 *
 * @author christoph
 */
public class POSinppetFactory {

    public static BasicPOSnippetFactory getBasicFactory(
            InformationFlowContract contract,
            ProofObligationVars vars,
            Services services) {
        return new BasicPOSnippetFactoryImpl(contract, vars, services);
    }

    public static SymbExecPOSnippetFactory getSymbExecFactory(
            InformationFlowContract contract,
            JavaInfo javaInfo,
            ProofObligationVars vars,
            Services services) {
        return new SymbExecPOSnippetFactoryImpl(contract, javaInfo, vars, services);
    }

    public static InfFlowPOSnippetFactory getInfFlowFactory(
            InformationFlowContract contract,
            ProofObligationVars vars1,
            ProofObligationVars vars2,
            Services services) {
        return new InfFlowPOSnippetFactoryImpl(contract, vars1, vars2, services);
    }

    static BasicPOSnippetFactory getBasicFactory(
            BasicSnippetData data, ProofObligationVars poVars) {
        return new BasicPOSnippetFactoryImpl(data, poVars);
    }

}
