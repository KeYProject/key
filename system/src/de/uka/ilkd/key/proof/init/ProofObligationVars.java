/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import java.util.Collection;


/**
 * Prepare program and location variables.
 * <p/>
 * @author christoph
 * <p/>
 */
public class ProofObligationVars {

    protected static final TermBuilder TB = TermBuilder.DF;
    public final ImmutableList<Term> termList;
    public final String postfix;
    public final Term self;
    public final Term selfAtPost;
    public final ImmutableList<Term> params;
    public final Term result;
    public final Term resultAtPost;
    public final Term exception;
    public final Term exceptionAtPost;
    public final Term heap;
    public final Term heapAtPre;
    public final Term heapAtPost;
    public final Term mbyAtPre;


    ProofObligationVars(IProgramMethod pm,
                        KeYJavaType kjt, // contract.getKJT()
                        Services services) {
        this(pm, kjt, "", services);
    }


    public ProofObligationVars(Term self,
                               Term selfAtPost,
                               ImmutableList<Term> params,
                               Term result,
                               Term resultAtPost,
                               Term exception,
                               Term exceptionAtPost,
                               Term heap,
                               Term heapAtPre,
                               Term heapAtPost,
                               String postfix,
                               Services services) {
        this.postfix = postfix;

        this.self = self;
        this.selfAtPost = selfAtPost;
        this.params = params;
        this.result = result;
        this.resultAtPost = resultAtPost;
        this.exception = exception;
        this.exceptionAtPost = exceptionAtPost;
        this.heap = heap;
        this.heapAtPre = heapAtPre;
        this.heapAtPost = heapAtPost;

        final Sort intSort =
                services.getTypeConverter().getIntegerLDT().targetSort();
        final Function mbyAtPreFunc =
                new Function(new Name(TB.newName(services, "mbyAtPre")), intSort);
        register(mbyAtPreFunc, services);
        this.mbyAtPre = TB.func(mbyAtPreFunc);


        ImmutableList<Term> terms =
                ImmutableSLList.<Term>nil();
        terms = terms.append(self);
        terms = terms.append(selfAtPost);
        terms = terms.append(params);
        terms = terms.append(result);
        terms = terms.append(resultAtPost);
        terms = terms.append(exception);
        terms = terms.append(exceptionAtPost);
        terms = terms.append(heap);
        terms = terms.append(heapAtPre);
        terms = terms.append(heapAtPost);
        terms = terms.append(mbyAtPre);
        termList = terms;
    }


    public ProofObligationVars(Term self,
                               Term selfAtPost,
                               Collection<Term> localVars,
                               Term result,
                               Term resultAtPost,
                               Term exception,
                               Term exceptionAtPost,
                               Term heap,
                               Term heapAtPre,
                               Term heapAtPost,
                               String postfix,
                               Services services) {
        this(self, selfAtPost, toList(localVars), result, resultAtPost, exception,
             exceptionAtPost, heap, heapAtPre, heapAtPost, postfix, services);
    }


    static ImmutableList<Term> toList(Collection<Term> localVars) {
        ImmutableList<Term> res = ImmutableSLList.<Term>nil();
        for (Term var : localVars) {
            res = res.append(var);
        }
        return res;
    }


    public ProofObligationVars(IProgramMethod pm,
                               KeYJavaType kjt,
                               Term self,
                               Term selfAtPost,
                               ImmutableList<Term> params,
                               Term result,
                               Term resultAtPost,
                               Term heap,
                               Term heapAtPre,
                               Term heapAtPost,
                               String postfix,
                               Services services) {
        this(pm, kjt, self, selfAtPost, params, result, resultAtPost, heap,
             heapAtPre, heapAtPost, postfix, services, true);
    }


    public ProofObligationVars(IProgramMethod pm,
                               KeYJavaType kjt,
                               Term self,
                               Term selfAtPost,
                               ImmutableList<Term> params,
                               Term result,
                               Term resultAtPost,
                               Term heap,
                               Term heapAtPre,
                               Term heapAtPost,
                               String postfix,
                               Services services,
                               boolean register) {
        this(self, selfAtPost, params, result, resultAtPost,
             TB.var(TB.excVar(services, "exc" + postfix, pm, true)),
             TB.var(TB.excVar(services, "excAtPost" + postfix, pm, true)),
             heap, heapAtPre, heapAtPost, postfix, services);


        if (register) {
            //register the variables so they are declared in proof header
            //if the proof is saved to a file
            if (self != null) {
                register(this.self.op(ProgramVariable.class), services);
            }
            register(exception.op(ProgramVariable.class), services);
            register(exceptionAtPost.op(ProgramVariable.class), services);
            if (!heap.equals(TB.getBaseHeap(services))) {
                register(heap.op(LocationVariable.class), services);
            }
        }
    }


    ProofObligationVars(IProgramMethod pm,
                        KeYJavaType kjt,
                        String postfix,
                        Services services) {
        this(pm, kjt,
             TB.selfVar(services, pm, kjt, true, postfix) != null ?
                 TB.var(TB.selfVar(services, pm, kjt, true, postfix)) :
                 null,
             TB.selfVar(services, pm, kjt, true, postfix) != null ?
                 TB.var(TB.selfVar(services, pm, kjt, true, "AtPost" + postfix)) :
                 null,
             TB.var(TB.paramVars(services, postfix, pm, true)),
             (!pm.isVoid() && !pm.isConstructor()) ?
                 TB.var(TB.resultVar(services, "result" + postfix, pm, true)) :
                 null,
             (!pm.isVoid() && !pm.isConstructor()) ?

             TB.var(TB.resultVar(services, "resultAtPost" + postfix, pm, true)) :
                 null,
             "".equals(postfix) ?
                 TB.getBaseHeap(services) :
                 TB.var(TB.heapAtPreVar(services, "heap" + postfix, true)),
             TB.var(TB.heapAtPreVar(services, "heapAtPre" + postfix, true)),
             TB.var(TB.heapAtPreVar(services, "heapAtPost" + postfix, true)),
             postfix,
             services);

        //register the variables so they are declared in proof header
        //if the proof is saved to a file
        register(ops(params, ProgramVariable.class), services);
        if (result != null) {
            register(result.op(ProgramVariable.class), services);
        }
        if (resultAtPost != null) {
            register(resultAtPost.op(ProgramVariable.class), services);
        }
        register(heapAtPre.op(LocationVariable.class), services);
        register(heapAtPost.op(LocationVariable.class), services);
    }


    protected final void register(ProgramVariable pv,
                                  Services services) {
        Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    protected final void register(ImmutableList<ProgramVariable> pvs,
                                  Services services) {
        for (ProgramVariable pv : pvs) {
            register(pv, services);
        }
    }


    protected final void register(Function f,
                                  Services services) {
        Namespace functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != Sort.UPDATE;
            if (f.sort() == Sort.FORMULA) {
                functionNames.addSafely(f);
            } else {
                functionNames.addSafely(f);
            }
        }
    }


    protected static <T> ImmutableList<T> ops(ImmutableList<Term> terms,
                                              Class<T> opClass)
            throws IllegalArgumentException {
        ImmutableList<T> ops = ImmutableSLList.<T>nil();
        for (Term t : terms) {
            ops = ops.append(t.op(opClass));
        }
        return ops;
    }
}
