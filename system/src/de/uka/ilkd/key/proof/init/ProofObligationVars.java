/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.AnonHeapTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;


/**
 *
 * @author christoph
 */
public class ProofObligationVars {

    /** Variables for the pre and post condition. */
    public final StateVars pre, post;

    /** Exception Variable for the try-catch statement. */
    public final Term exceptionParameter;

    /** The formal parameters of a method. */
    public final ImmutableList<Term> formalParams;

    /** If this object was created form another ProofObligationVars
     *  object by adding a postfix to the variable names, then this
     *  variable contains the used postfix.
     */
    public final String postfix;


    public ProofObligationVars(IProgramMethod pm,
                               KeYJavaType kjt,
                               Services services) {
        this.pre = StateVars.buildMethodContractPreVars(pm, kjt, services);
        this.post = StateVars.buildMethodContractPostVars(this.pre, pm, kjt, services);
        this.exceptionParameter = buildExceptionParameter(services);
        this.formalParams = buildFormalParamVars(services);
        this.postfix = "";
    }


    public ProofObligationVars(ProofObligationVars orig,
                               String postfix,
                               Services services) {
        this.pre = StateVars.buildInfFlowPreVars(orig.pre, postfix, services);
        this.post = StateVars.buildInfFlowPostVars(orig.pre, orig.post, pre, postfix, services);
        this.exceptionParameter = buildExceptionParameter(services);
        this.formalParams = orig.formalParams != null ?
                            buildFormalParamVars(services) : null;
        this.postfix = postfix;
    }


    public ProofObligationVars(StateVars pre,
                               StateVars post,
                               Term exceptionParameter,
                               ImmutableList<Term> formalParams) {
        this.pre = pre;
        this.post = post;
        this.exceptionParameter = exceptionParameter;
        this.formalParams = formalParams;
        this.postfix = "";
    }

    public ProofObligationVars(StateVars pre,
                               StateVars post,
                               Services services) {
        this.pre = pre;
        this.post = post;
        this.postfix = "";
        this.exceptionParameter = buildExceptionParameter(services);
        // formal parameters are need only for proof obligations
        // of methods
        this.formalParams = null;
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
            return new ProofObligationVars(newPre, post, exceptionParameter, formalParams);
        } else {
            return this;
        }
    }


    /**
     * Build variable for try statement.
     * @param services  the services object.
     * @return  the generated variable.
     */
    private Term buildExceptionParameter(Services services) {
        JavaInfo javaInfo = services.getJavaInfo();
        final KeYJavaType eType =
            javaInfo.getTypeByClassName("java.lang.Exception");
        final ProgramElementName ePEN = new ProgramElementName("e");
        return TermBuilder.DF.var(new LocationVariable(ePEN, eType));
    }

    /**
     * Create formal parameters.
     * @throws IllegalArgumentException
     */
    private ImmutableList<Term> buildFormalParamVars(
            Services services) throws IllegalArgumentException {
        ImmutableList<Term> formalParamVars = ImmutableSLList.<Term>nil();
        for (Term param : pre.localVars) {
            ProgramVariable paramVar = param.op(ProgramVariable.class);
            ProgramElementName pen = new ProgramElementName("_" +
                     paramVar.name());
            LocationVariable formalParamVar =
                    new LocationVariable(pen, paramVar.getKeYJavaType());
            register(formalParamVar, services);
            Term formalParam = TermBuilder.DF.var(formalParamVar);
            formalParamVars = formalParamVars.append(formalParam);
// The following line raises a null pointer exception because getProof()
// might return null
//              tb.getServices().getProof().addIFSymbol(formalParamVar);
        }
        return formalParamVars;
    }


    static void register(ProgramVariable pv,
                         Services services) {
        Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }
}
