/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.SpecificationElement;


/**
 * Generate term "self != null".
 * <p/>
 * @author christoph
 */
abstract class TwoStateMethodPredicateSnippet implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        IProgramMethod pm = null;
        Function contApplPred = null;
        if (d.contract instanceof Contract) {
            pm = (IProgramMethod) ((Contract) d.contract).getTarget();
            contApplPred = generateContApplPredicate((Contract) d.contract, d.tb);
            return instantiateContApplPredicate(contApplPred, poVars, pm, d.tb);
        } else if (d.contract instanceof LoopInvariant) {
            pm = (IProgramMethod) ((LoopInvariant) d.contract).getTarget();
            contApplPred = generateLoopApplPredicate((LoopInvariant) d.contract, d.tb);
            return instantiateLoopApplPredicate(contApplPred, poVars, pm, d.tb);
        }
        return null;        
    }


    private Function generateContApplPredicate(Contract contract,
                                               TermBuilder.Serviced tb) {
        String nameString = generatePredicateName(contract);
        IProgramMethod pm = (IProgramMethod) contract.getTarget();
        final Name name = new Name(nameString);
        final JavaInfo javaInfo = tb.getServices().getJavaInfo();
        final Namespace functionNS =
                tb.getServices().getNamespaces().functions();
        Function pred = (Function) functionNS.lookup(name);

        if (pred == null) {
            // Arguments: params, heapAtPre, exception, heapAtPost
            int length = pm.getParamTypes().size() + 3;
            if (!pm.isStatic()) {
                // Arguments: + self
                length++;
            }
            if (!pm.isVoid() && !pm.isConstructor()) {
                // Arguments: + result
                length++;
            }
            Sort[] predArgSorts =
                    new Sort[length];

            int i = 0;
            if (!pm.isStatic()) {
                // type of self
                predArgSorts[i++] = pm.getContainerType().getSort();
            }
            // types of params
            for (KeYJavaType t : pm.getParamTypes()) {
                predArgSorts[i++] = t.getSort();
            }
            // type of heapAtPre
            predArgSorts[i++] = tb.getBaseHeap().sort();
            if (!pm.isVoid() && !pm.isConstructor()) {
                // type of result
                predArgSorts[i++] = pm.getReturnType().getSort();
            }
            // type of exception
            predArgSorts[i++] =
                    javaInfo.getTypeByClassName("java.lang.Exception").getSort();
            // type of heapAtPost
            predArgSorts[i++] = tb.getBaseHeap().sort();

            pred = new Function(name, Sort.FORMULA, predArgSorts);
            tb.getServices().getNamespaces().functions().addSafely(pred);
        }
        return pred;
    }
    
    
    private Function generateLoopApplPredicate(LoopInvariant loopInv,
            TermBuilder.Serviced tb) {
        String nameString = generatePredicateName(loopInv);
        IProgramMethod pm = (IProgramMethod) loopInv.getTarget();
        final Name name = new Name(nameString);        
        final Namespace functionNS =
            tb.getServices().getNamespaces().functions();
        Function pred = (Function) functionNS.lookup(name);

        if (pred == null) {
            // Arguments: local variables, heapAtPre, heapAtPost
            int length =  loopInv.getParams().size() + loopInv.getResults().size() + 2;
            if (!pm.isStatic()) {
                // Arguments: + self
                length++;
            }
            
            Sort[] predArgSorts =
                new Sort[length];

            int i = 0;
            if (!pm.isStatic()) {
                // type of self
                predArgSorts[i++] = loopInv.getInternalSelfTerm().sort();
            }
            // types of local variables (in)
            for (Term t : loopInv.getParams()) {
                predArgSorts[i++] = t.sort();
            }
            // type of heapAtPre
            predArgSorts[i++] = tb.getBaseHeap().sort();
            
            // types of local variables (out)
            for(Term t : loopInv.getResults()){
                predArgSorts[i++] = t.sort();
            }
            
            // type of heapAtPost
            predArgSorts[i++] = tb.getBaseHeap().sort();

            pred = new Function(name, Sort.FORMULA, predArgSorts);
            tb.getServices().getNamespaces().functions().addSafely(pred);
        }
        return pred;
    }


    private Term instantiateContApplPredicate(Function pred,
                                              ProofObligationVars appData,
                                              IProgramMethod pm,
                                              TermBuilder.Serviced tb) {
        Sort[] predArgSorts = new Sort[pred.argSorts().size()];
        pred.argSorts().toArray(predArgSorts);
        Term[] predArgs = new Term[predArgSorts.length];

        int i = 0;
        ImmutableList<Term> params = appData.params;

        if (!pm.isStatic()) {
            // self
            predArgs[i++] = appData.self;
        }
        // params
        for (KeYJavaType t : pm.getParamTypes()) {
            predArgSorts[i] = t.getSort();
            predArgs[i++] = params.head();
            params = params.tail();
        }
        // heapAtPre
        predArgs[i++] = appData.heapAtPre;
        if (!pm.isVoid() && !pm.isConstructor()) {
            // result
            predArgs[i++] = appData.results.head();
        }
        // exception
        predArgs[i++] = appData.exception;
        // heapAtPost
        predArgs[i++] = appData.heapAtPost;

        return tb.func(pred, predArgs);
    }
    
    
    private Term instantiateLoopApplPredicate(Function pred,
            ProofObligationVars appData,
            IProgramMethod pm,
            TermBuilder.Serviced tb) {
        Sort[] predArgSorts = new Sort[pred.argSorts().size()];
        pred.argSorts().toArray(predArgSorts);
        Term[] predArgs = new Term[predArgSorts.length];

        int i = 0;
        ImmutableList<Term> params = appData.params;
        ImmutableList<Term> results = appData.results;

        if (!pm.isStatic()) {
            // self
            predArgs[i++] = appData.self;
        }
        // params
        for (Term t : appData.params) {
            predArgSorts[i] = t.sort();
            predArgs[i++] = params.head();
            params = params.tail();
        }
        // heapAtPre
        predArgs[i++] = appData.heapAtPre;
        //if (!pm.isVoid() && !pm.isConstructor()) {
            // result
        //    predArgs[i++] = appData.results.head();
        //}
        for (Term t : appData.results) {
            predArgSorts[i] = t.sort();
            predArgs[i++] = results.head();
            params = results.tail();
        }
        
        // heapAtPost
        predArgs[i++] = appData.heapAtPost;

        return tb.func(pred, predArgs);
    }


    abstract String generatePredicateName(SpecificationElement contract);

}
