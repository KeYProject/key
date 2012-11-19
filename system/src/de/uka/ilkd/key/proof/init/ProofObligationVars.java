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
    public final ImmutableList<Term> paddedTermList;
    public final ImmutableList<Term> paddedTermListWithoutLocalVars;
    public final String postfix;
    public final Term self;
    public final Term selfAtPost;
    public final ImmutableList<Term> localIns;
    public final ImmutableList<Term> localOuts;
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
                               ImmutableList<Term> localIns,
                               ImmutableList<Term> localOuts,
                               Term result,
                               Term resultAtPost,
                               Term exception,
                               Term exceptionAtPost,
                               Term heap,
                               Term heapAtPre,
                               Term heapAtPost,
                               Term mbyAtPre,
                               String postfix,
                               Services services) {
        this.postfix = postfix;

        this.self = self;
        this.selfAtPost = selfAtPost;
        this.localIns = localIns;
        this.localOuts = localOuts;
        this.result = result;
        this.resultAtPost = resultAtPost;
        this.exception = exception;
        this.exceptionAtPost = exceptionAtPost;
        this.heap = heap;
        this.heapAtPre = heapAtPre;
        this.heapAtPost = heapAtPost;
        this.mbyAtPre = mbyAtPre;


        ImmutableList<Term> terms =
                ImmutableSLList.<Term>nil();
        terms = appendIfNotNull(terms, heap);
        terms = appendIfNotNull(terms, self);
        terms = appendIfNotNull(terms, selfAtPost);
        terms = terms.append(localIns);
        terms = appendIfNotNull(terms, heapAtPre);
        terms = terms.append(localOuts);
        terms = appendIfNotNull(terms, result);
        terms = appendIfNotNull(terms, resultAtPost);
        terms = appendIfNotNull(terms, exception);
        terms = appendIfNotNull(terms, exceptionAtPost);
        terms = appendIfNotNull(terms, heapAtPost);
        terms = appendIfNotNull(terms, mbyAtPre);
        termList = terms;

        ImmutableList<Term> allTerms =
                ImmutableSLList.<Term>nil();
        allTerms = allTerms.append(heap);
        allTerms = allTerms.append(self);
        allTerms = allTerms.append(selfAtPost);
        allTerms = allTerms.append(localIns);
        allTerms = allTerms.append(heapAtPre);
        allTerms = allTerms.append(localOuts);
        allTerms = allTerms.append(result);
        allTerms = allTerms.append(resultAtPost);
        allTerms = allTerms.append(exception);
        allTerms = allTerms.append(exceptionAtPost);
        allTerms = allTerms.append(heapAtPost);
        allTerms = allTerms.append(mbyAtPre);
        paddedTermList = allTerms;

        ImmutableList<Term> allTermsButLocalVars =
                ImmutableSLList.<Term>nil();
        allTermsButLocalVars = allTermsButLocalVars.append(heap);
        allTermsButLocalVars = allTermsButLocalVars.append(self);
        allTermsButLocalVars = allTermsButLocalVars.append(selfAtPost);
        allTermsButLocalVars = allTermsButLocalVars.append(heapAtPre);
        allTermsButLocalVars = allTermsButLocalVars.append(result);
        allTermsButLocalVars = allTermsButLocalVars.append(resultAtPost);
        allTermsButLocalVars = allTermsButLocalVars.append(exception);
        allTermsButLocalVars = allTermsButLocalVars.append(exceptionAtPost);
        allTermsButLocalVars = allTermsButLocalVars.append(heapAtPost);
        allTermsButLocalVars = allTermsButLocalVars.append(mbyAtPre);
        paddedTermListWithoutLocalVars = allTermsButLocalVars;
    }


    private ImmutableList<Term> appendIfNotNull(ImmutableList<Term> list,
                                                Term t) {
        if (t != null) {
            return list.append(t);
        } else {
            return list;
        }
    }


    public ProofObligationVars(Term baseHeap,
                               Term self,
                               ImmutableList<Term> localIns,
                               Term heapAtPre,
                               ImmutableList<Term> localOuts,
                               Term result,
                               Term exception,
                               Term heapAtPost,
                               Services services) {
        this(self, null, localIns, localOuts, result, null, exception, null,
             baseHeap, heapAtPre, heapAtPost, null, "", services);
    }


    public ProofObligationVars(Term self,
                               ImmutableList<Term> params,
                               Term result,
                               Term exception,
                               Term heap,
                               Services services) {
        this(self, null, params, ImmutableSLList.<Term>nil(), result, null,
             exception, null, heap, null, null, null, "", services);
    }


    ProofObligationVars(IProgramMethod pm,
                        KeYJavaType kjt,
                        String postfix,
                        Services services) {
        this(buildSelfVar(services, pm, kjt, postfix),
             buildSelfAtPostVar(services, pm, kjt, postfix),
             buildParamVars(services, postfix, pm),
             ImmutableSLList.<Term>nil(), // no local out variables
             buildResultVar(pm, services, postfix),
             buildResultAtPostVar(pm, services, postfix),
             buildExceptionVar(services, postfix, pm),
             buildExceptionAtPostVar(services, postfix, pm),
             buildHeapVar(postfix, services),
             buildHeapAtPreVar(services, postfix),
             buildHeapAtPostVar(services, postfix),
             buildMbyVar(services),
             postfix,
             services);
    }


    private static Term buildSelfVar(Services services,
                                     IProgramMethod pm,
                                     KeYJavaType kjt,
                                     String postfix) {
        if (pm.isStatic() || pm.isConstructor()) {
            return null;
        }
        Term selfVar = TB.var(TB.selfVar(services, pm, kjt, true, postfix));
        register(selfVar.op(ProgramVariable.class), services);
        return selfVar;
    }


    private static Term buildSelfAtPostVar(Services services,
                                           IProgramMethod pm,
                                           KeYJavaType kjt,
                                           String postfix) {
        if (pm.isStatic()) {
            return null;
        }
        Term selfAtPostVar =
                TB.var(TB.selfVar(services, pm, kjt, true, "AtPost" + postfix));
        register(selfAtPostVar.op(ProgramVariable.class), services);
        return selfAtPostVar;
    }


    private static ImmutableList<Term> buildParamVars(Services services,
                                                      String postfix,
                                                      IProgramMethod pm) {
        ImmutableList<Term> paramVars =
                TB.var(TB.paramVars(services, postfix, pm, true));
        register(ops(paramVars, ProgramVariable.class), services);
        return paramVars;
    }


    private static Term buildResultVar(IProgramMethod pm,
                                       Services services,
                                       String postfix) {
        if (pm.isVoid() || pm.isConstructor()) {
            return null;
        }
        Term resultVar =
                TB.var(TB.resultVar(services, "result" + postfix, pm, true));
        register(resultVar.op(ProgramVariable.class), services);
        return resultVar;
    }


    private static Term buildResultAtPostVar(IProgramMethod pm,
                                             Services services,
                                             String postfix) {
        if (pm.isVoid() || pm.isConstructor()) {
            return null;
        }
        Term resultAtPostVar =
                TB.var(TB.resultVar(services, "resultAtPost" + postfix, pm, true));
        register(resultAtPostVar.op(ProgramVariable.class), services);
        return resultAtPostVar;
    }


    private static Term buildHeapVar(String postfix,
                                     Services services) {
        if ("".equals(postfix)) {
            return TB.getBaseHeap(services);
        } else {
            Term heapVar =
                    TB.var(TB.heapAtPreVar(services, "heap" + postfix, true));
            register(heapVar.op(LocationVariable.class), services);
            return heapVar;
        }
    }


    private static Term buildHeapAtPreVar(Services services,
                                          String postfix) {
        Term heapAtPreVar =
                TB.var(TB.heapAtPreVar(services, "heapAtPre" + postfix, true));
        register(heapAtPreVar.op(LocationVariable.class), services);
        return heapAtPreVar;
    }


    private static Term buildHeapAtPostVar(Services services,
                                           String postfix) {
        Term heapAtPostVar =
                TB.var(TB.heapAtPreVar(services, "heapAtPost" + postfix, true));
        register(heapAtPostVar.op(LocationVariable.class), services);
        return heapAtPostVar;
    }


    private static Term buildExceptionVar(Services services,
                                          String postfix,
                                          IProgramMethod pm) {
        Term excVar = TB.var(TB.excVar(services, "exc" + postfix, pm, true));
        register(excVar.op(ProgramVariable.class), services);
        return excVar;
    }


    private static Term buildExceptionAtPostVar(Services services,
                                                String postfix,
                                                IProgramMethod pm) {
        Term excVarAtPost =
                TB.var(TB.excVar(services, "excAtPost" + postfix, pm, true));
        register(excVarAtPost.op(ProgramVariable.class), services);
        return excVarAtPost;
    }


    private static Term buildMbyVar(Services services) {
        final Sort intSort =
                services.getTypeConverter().getIntegerLDT().targetSort();
        final Function mbyAtPreFunc =
                new Function(new Name(TB.newName(services, "mbyAtPre")), intSort);
        register(mbyAtPreFunc, services);
        return TB.func(mbyAtPreFunc);
    }


    static void register(ProgramVariable pv,
                         Services services) {
        Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    static void register(ImmutableList<ProgramVariable> pvs,
                         Services services) {
        for (ProgramVariable pv : pvs) {
            register(pv, services);
        }
    }


    static void register(Function f,
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


    static <T> ImmutableList<T> ops(ImmutableList<Term> terms,
                                    Class<T> opClass)
            throws IllegalArgumentException {
        ImmutableList<T> ops = ImmutableSLList.<T>nil();
        for (Term t : terms) {
            ops = ops.append(t.op(opClass));
        }
        return ops;
    }
}
