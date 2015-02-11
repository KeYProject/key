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
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
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

    private final TermBuilder tb;


    public ProofObligationVars(IProgramMethod pm,
                               KeYJavaType kjt,
                               Services services) {
        this.pre = StateVars.buildMethodContractPreVars(pm, kjt, services);
        this.post = StateVars.buildMethodContractPostVars(this.pre, pm, kjt, services);
        this.tb = services.getTermBuilder();
        this.exceptionParameter = buildExceptionParameter(services);
        this.formalParams = buildFormalParamVars(services);
        this.postfix = "";
    }


    public ProofObligationVars(ProofObligationVars orig,
                               String postfix,
                               Services services) {
        this.pre = StateVars.buildInfFlowPreVars(orig.pre, postfix, services);
        this.post = StateVars.buildInfFlowPostVars(orig.pre, orig.post, pre, postfix, services);
        this.tb = services.getTermBuilder();
        this.exceptionParameter = buildExceptionParameter(services);
        this.formalParams = orig.formalParams != null ?
                            buildFormalParamVars(services) : null;
        this.postfix = postfix;
    }


    public ProofObligationVars(StateVars pre,
                               StateVars post,
                               Term exceptionParameter,
                               ImmutableList<Term> formalParams,
                               Services services) {
        this.pre = pre;
        this.post = post;
        this.exceptionParameter = exceptionParameter;
        this.formalParams = formalParams;
        this.postfix = "";
        this.tb = services.getTermBuilder();
    }

    public ProofObligationVars(StateVars pre,
                               StateVars post,
                               Term exceptionParameter,
                               ImmutableList<Term> formalParams,
                               TermBuilder tb) {
        this.pre = pre;
        this.post = post;
        this.exceptionParameter = exceptionParameter;
        this.formalParams = formalParams;
        this.postfix = "";
        this.tb = tb;
    }

    public ProofObligationVars(StateVars pre,
                               StateVars post,
                               Services services) {
        this.pre = pre;
        this.post = post;
        this.postfix = "";
        this.tb = services.getTermBuilder();
        this.exceptionParameter = buildExceptionParameter(services);
        // formal parameters are need only for proof obligations
        // of methods
        this.formalParams = null;
    }

    public ProofObligationVars labelHeapAtPreAsAnonHeapFunc() {
        if (pre.heap.op() instanceof Function &&
            !pre.heap.containsLabel(ParameterlessTermLabel.ANON_HEAP_LABEL)) {
            ImmutableArray<TermLabel> labels = pre.heap.getLabels();
            TermLabel[] newLabels = new TermLabel[labels.size()+1];
            labels.toArray(newLabels);
            newLabels[labels.size()] = ParameterlessTermLabel.ANON_HEAP_LABEL;
            StateVars newPre = new StateVars(pre.self, pre.guard,
                                             pre.localVars, pre.result,
                                             pre.exception,
                                             tb.label(pre.heap, new ImmutableArray<TermLabel>(newLabels)),
                                             pre.mbyAtPre);
            return new ProofObligationVars(newPre, post, exceptionParameter, formalParams, tb);
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
        return tb.var(new LocationVariable(ePEN, eType));
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
            Term formalParam = tb.var(formalParamVar);
            formalParamVars = formalParamVars.append(formalParam);
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
