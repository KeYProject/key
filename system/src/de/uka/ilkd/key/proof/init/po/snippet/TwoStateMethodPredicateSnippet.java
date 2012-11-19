/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofObligationVars;


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
        final IProgramMethod pm = (IProgramMethod) d.targetMethod;
        String nameString = generatePredicateName(pm, d.targetBlock);
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


    abstract String generatePredicateName(IProgramMethod pm,
                                          StatementBlock block);
}
