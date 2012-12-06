/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.LoopInvariant;


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
       IObserverFunction targetMethod =
               (IObserverFunction) d.get(BasicSnippetData.Key.TARGET_METHOD);
       final IProgramMethod pm = (IProgramMethod) targetMethod;
       StatementBlock targetBlock =
               (StatementBlock) d.get(BasicSnippetData.Key.TARGET_BLOCK);
       LoopInvariant loopInv =
               (LoopInvariant) d.get(BasicSnippetData.Key.LOOPINVARIANT);
       String nameString = generatePredicateName(pm, targetBlock, loopInv);
       final Function contApplPred =
               generateContApplPredicate(nameString, poVars.termList, d.tb);
       return instantiateContApplPredicate(contApplPred, poVars, d.tb);
   }


   private Function generateContApplPredicate(String nameString,
                                              ImmutableList<Term> termList,
                                              TermBuilder.Serviced tb) {
       final Name name = new Name(nameString);
       final Namespace functionNS =
               tb.getServices().getNamespaces().functions();
       Function pred = (Function) functionNS.lookup(name);

       if (pred == null) {
           Sort[] argSorts =
                   new Sort[termList.size()];

           int i = 0;
           for (Term arg : termList) {
               argSorts[i] = arg.sort();
               i++;
           }

           pred = new Function(name, Sort.FORMULA, argSorts);
           tb.getServices().getNamespaces().functions().addSafely(pred);
       }
       return pred;
   }


   private Term instantiateContApplPredicate(Function pred,
                                             ProofObligationVars appData,
                                             TermBuilder.Serviced tb) {
       Sort[] predArgSorts = new Sort[pred.argSorts().size()];
       pred.argSorts().toArray(predArgSorts);
       Term[] predArgs = new Term[predArgSorts.length];

       int i = 0;
       for (Term arg : appData.termList) {
           predArgs[i] = arg;
           i++;
       }

       return tb.func(pred, predArgs);
   }
   /* Probably not necessary anymore, but you'll never know ;-)

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
//<<<<<<< HEAD
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
=======
        IObserverFunction targetMethod =
                (IObserverFunction) d.get(BasicSnippetData.Key.TARGET_METHOD);
        final IProgramMethod pm = (IProgramMethod) targetMethod;
        StatementBlock targetBlock =
                (StatementBlock) d.get(BasicSnippetData.Key.TARGET_BLOCK);
        String nameString = generatePredicateName(pm, targetBlock);
        final Function contApplPred =
                generateContApplPredicate(nameString, poVars.termList, d.tb);
        return instantiateContApplPredicate(contApplPred, poVars, d.tb);
    }


    private Function generateContApplPredicate(String nameString,
                                               ImmutableList<Term> termList,
                                               TermBuilder.Serviced tb) {
        final Name name = new Name(nameString);
>>>>>>> 7f64f84cfbe7566c50d8bf4b6e6613a3a60fa3f6
        final Namespace functionNS =
                tb.getServices().getNamespaces().functions();
        Function pred = (Function) functionNS.lookup(name);

        if (pred == null) {
            Sort[] argSorts =
                    new Sort[termList.size()];

            int i = 0;
            for (Term arg : termList) {
                argSorts[i] = arg.sort();
                i++;
            }

            pred = new Function(name, Sort.FORMULA, argSorts);
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
                                              TermBuilder.Serviced tb) {
        Sort[] predArgSorts = new Sort[pred.argSorts().size()];
        pred.argSorts().toArray(predArgSorts);
        Term[] predArgs = new Term[predArgSorts.length];

        int i = 0;
        for (Term arg : appData.termList) {
            predArgs[i] = arg;
            i++;
        }
//<<<<<<< HEAD
        // heapAtPre
        predArgs[i++] = appData.heapAtPre;
        if (!pm.isVoid() && !pm.isConstructor()) {
            // result
            predArgs[i++] = appData.result;// .results.head();
        }
        // exception
        predArgs[i++] = appData.exception;
        // heapAtPost
        predArgs[i++] = appData.heapAtPost;
=======
>>>>>>> 7f64f84cfbe7566c50d8bf4b6e6613a3a60fa3f6

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
        ImmutableList<Term> params = appData.localIns;//.params;
        ImmutableList<Term> results = appData.localOuts;//.results;

        if (!pm.isStatic()) {
            // self
            predArgs[i++] = appData.self;
        }
        // params
        for (Term t : params) {
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
        for (Term t : results) {
            predArgSorts[i] = t.sort();
            predArgs[i++] = results.head();
            params = results.tail();
        }
        
        // heapAtPost
        predArgs[i++] = appData.heapAtPost;

        return tb.func(pred, predArgs);
    }*/
    abstract String generatePredicateName(IProgramMethod pm,
                                          StatementBlock block,
                                          LoopInvariant loopInv);
}
