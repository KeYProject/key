/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;


/**
 *
 * @author christoph
 */
public class ProofObligationVars {

    public final StateVars pre, post;

    public final String postfix;


    public ProofObligationVars(IProgramMethod pm,
                               KeYJavaType kjt,
                               Services services) {
        this.pre = StateVars.buildMethodContractPreVars(pm, kjt, services);
        this.post = StateVars.buildMethodContractPostVars(this.pre, pm, kjt, services);
        this.postfix = "";
    }


    public ProofObligationVars(ProofObligationVars orig,
                               String postfix,
                               Services services) {
        this.pre = StateVars.buildInfFlowPreVars(orig.pre, postfix, services);
        this.post = StateVars.buildInfFlowPostVars(orig.pre, orig.post, pre, postfix, services);
        this.postfix = postfix;
    }


    public ProofObligationVars(StateVars pre,
                               StateVars post) {
        this.pre = pre;
        this.post = post;
        this.postfix = "";
    }
}
