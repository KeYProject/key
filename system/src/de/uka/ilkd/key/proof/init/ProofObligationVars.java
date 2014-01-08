/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.AnonHeapTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;


/**
 *
 * @author christoph
 */
public class ProofObligationVars {

    public final StateVars pre, post;
    public final Term catchVar;

    public final String postfix;


    public ProofObligationVars(IProgramMethod pm,
                               KeYJavaType kjt,
                               Services services) {
        this.pre = StateVars.buildMethodContractPreVars(pm, kjt, services);
        this.post = StateVars.buildMethodContractPostVars(this.pre, pm, kjt, services);

        // create variable for try statement
        JavaInfo javaInfo = services.getJavaInfo();
        final KeYJavaType eType =
            javaInfo.getTypeByClassName("java.lang.Exception");
        final ProgramElementName ePEN = new ProgramElementName("e");
        catchVar = TermBuilder.DF.var(new LocationVariable(ePEN, eType));

        this.postfix = "";
    }


    public ProofObligationVars(ProofObligationVars orig,
                               String postfix,
                               Services services) {
        this.pre = StateVars.buildInfFlowPreVars(orig.pre, postfix, services);
        this.post = StateVars.buildInfFlowPostVars(orig.pre, orig.post, pre, postfix, services);

        // create variable for try statement
        JavaInfo javaInfo = services.getJavaInfo();
        final KeYJavaType eType =
            javaInfo.getTypeByClassName("java.lang.Exception");
        final ProgramElementName ePEN =
                new ProgramElementName(orig.catchVar.toString()); // + postfix);
        catchVar = TermBuilder.DF.var(new LocationVariable(ePEN, eType));

        this.postfix = postfix;
    }


    public ProofObligationVars(StateVars pre,
                               StateVars post,
                               Term catchVar) {
        this.pre = pre;
        this.post = post;
        this.catchVar = catchVar;
        this.postfix = "";
    }

    public ProofObligationVars(StateVars pre,
                               StateVars post,
                               Services services) {
        this.pre = pre;
        this.post = post;
        this.postfix = "";

        // build variable for try statement
        JavaInfo javaInfo = services.getJavaInfo();
        final KeYJavaType eType =
            javaInfo.getTypeByClassName("java.lang.Exception");
        final ProgramElementName ePEN = new ProgramElementName("e");
        catchVar = TermBuilder.DF.var(new LocationVariable(ePEN, eType));
    }

    public ProofObligationVars labelHeapAtPreAsAnonHeapFunc() {
            final TermBuilder TB = TermBuilder.DF;
        if (pre.heap.op() instanceof Function &&
            !pre.heap.containsLabel(AnonHeapTermLabel.INSTANCE)) {
            ImmutableArray<ITermLabel> labels = pre.heap.getLabels();
            ITermLabel[] newLabels = new ITermLabel[labels.size()+1];
            labels.toArray(newLabels);
            newLabels[labels.size()] = AnonHeapTermLabel.INSTANCE;
            StateVars newPre = new StateVars(pre.self, pre.guard,
                                             pre.localVars, pre.result,
                                             pre.exception,
                                             TB.label(pre.heap, new ImmutableArray<ITermLabel>(newLabels)),
                                             pre.mbyAtPre);
            return new ProofObligationVars(newPre, post, catchVar);
        } else {
            return this;
        }
    }
}
