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
        this.pre = new StateVars(pm, kjt, "AtPre", services);
        this.post = new StateVars(pm, kjt, "AtPost", services);
        this.postfix = "";
    }


    public ProofObligationVars(ProofObligationVars orig,
                               String postfix,
                               Services services) {
        this.pre = new StateVars(orig.pre, postfix, services);
        this.post = new StateVars(orig.post, postfix, services);
        this.postfix = postfix;
    }


    public ProofObligationVars(StateVars pre,
                               StateVars post) {
        this.pre = pre;
        this.post = post;
        this.postfix = "";
    }
}
