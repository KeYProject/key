package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
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
import de.uka.ilkd.key.speclang.LoopSpecification;


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
        LoopSpecification loopInv =
                (LoopSpecification) d.get(BasicSnippetData.Key.LOOP_INVARIANT);
        String nameString = generatePredicateName(pm, targetBlock, loopInv);
        final ImmutableList<Term> termList =
                extractTermListForPredicate(pm, poVars, d.hasMby);
        final Sort[] argSorts =
                generateContApplArgumentSorts(termList, pm);
        final Function contApplPred =
                generateContApplPredicate(nameString, argSorts, d.tb, d.services);
        return instantiateContApplPredicate(contApplPred, termList, d.tb);
    }

    protected Sort[] generateContApplArgumentSorts(
            ImmutableList<Term> termList, IProgramMethod pm) {

        Sort[] argSorts = new Sort[termList.size()];
        //ImmutableArray<Sort> pmSorts = pm.argSorts();

        int i = 0;
        for (final Term arg : termList) {
            argSorts[i] = arg.sort();
            i++;
        }

        return argSorts;
    }


    private Function generateContApplPredicate(String nameString,
                                               Sort[] argSorts,
                                               TermBuilder tb,
                                               Services services) {
        final Name name = new Name(nameString);
        Namespace<Function> functionNS = services.getNamespaces().functions();

        /* This predicate needs to present on all branches and, therefore, must be added
         * to the toplevel function namespace. Hence, we rewind to the parent namespace here.
         */
        while(functionNS.parent() != null)
            functionNS = functionNS.parent();

        Function pred = (Function) functionNS.lookup(name);

        if (pred == null) {
            pred = new Function(name, Sort.FORMULA, argSorts);
            functionNS.addSafely(pred);
        }
        return pred;
    }


    private Term instantiateContApplPredicate(Function pred,
                                              ImmutableList<Term> termList,
                                              TermBuilder tb) {
        final Sort[] predArgSorts = new Sort[pred.argSorts().size()];
        pred.argSorts().toArray(predArgSorts);
        Term[] predArgs = new Term[predArgSorts.length];

        int i = 0;
        for (final Term arg : termList) {
            predArgs[i] = arg;
            i++;
        }

        return tb.func(pred, predArgs);
    }


    abstract String generatePredicateName(IProgramMethod pm,
                                          StatementBlock block,
                                          LoopSpecification loopInv);


    /**
     * Parameters and the result of a method only have to appear once in the
     * predicate. This method chooses the right variables out of the poVars.
     * @param poVars    The proof obligation variables.
     * @return
     */
    private ImmutableList<Term> extractTermListForPredicate(
            IProgramMethod pm,
            ProofObligationVars poVars,
            boolean hasMby) {
        ImmutableList<Term> relevantPreVars = ImmutableSLList.<Term>nil();
        ImmutableList<Term> relevantPostVars = ImmutableSLList.<Term>nil();

        if (!pm.isStatic()) {
            // self is relevant in the pre and post state for constructors
            // (if the method is static, then there is no self)
            relevantPreVars = relevantPreVars.append(poVars.pre.self);
            relevantPostVars = relevantPostVars.append(poVars.post.self);
        }

        // local variables which are not changed during execution or whose
        // changes are not observable (like for parameters) are relevant only
        // in the pre state
        Iterator<Term> localPostVarsIt = poVars.post.localVars.iterator();
        for (Term localPreVar : poVars.pre.localVars) {
            Term localPostVar = localPostVarsIt.next();
            relevantPreVars = relevantPreVars.append(localPreVar);
            if (localPostVar != localPreVar) {
                relevantPostVars = relevantPostVars.append(localPostVar);
            }
        }

        // guard term (for loop invariants) is relevant in the pre and
        // post state
        if (poVars.pre.guard != null) {
            // in case of an information flow loop invariant
            assert poVars.post.guard != null;
            relevantPreVars = relevantPreVars.append(poVars.pre.guard);
            relevantPostVars = relevantPostVars.append(poVars.post.guard);
        }

        // the result and possible exceptions are relevant only in the post
        // state
        if (poVars.post.result != null) {
            // method is not void
            relevantPostVars = relevantPostVars.append(poVars.post.result);
        }
        if (poVars.post.exception != null) {
            // TODO: only null for loop invariants?
            relevantPostVars = relevantPostVars.append(poVars.post.exception);
        }

        if (hasMby) {
            // if the contract has a measured by clause, then mbyAtPre is also
            // relevant
            relevantPreVars = relevantPreVars.append(poVars.pre.mbyAtPre);
        }

        // the heap is relevant in the pre and post state
        relevantPreVars = relevantPreVars.append(poVars.pre.heap);
        relevantPostVars = relevantPostVars.append(poVars.post.heap);

        return relevantPreVars.append(relevantPostVars);
    }
}