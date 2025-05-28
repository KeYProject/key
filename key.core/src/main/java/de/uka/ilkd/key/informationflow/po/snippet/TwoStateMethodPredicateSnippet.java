/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * Generate term "self != null".
 * <p/>
 *
 * @author christoph
 */
abstract class TwoStateMethodPredicateSnippet implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {

        IObserverFunction targetMethod =
            (IObserverFunction) d.get(BasicSnippetData.Key.TARGET_METHOD);
        final IProgramMethod pm = (IProgramMethod) targetMethod;
        StatementBlock targetBlock = (StatementBlock) d.get(BasicSnippetData.Key.TARGET_BLOCK);
        LoopSpecification loopInv = (LoopSpecification) d.get(BasicSnippetData.Key.LOOP_INVARIANT);
        String nameString = generatePredicateName(pm, targetBlock, loopInv);
        final ImmutableList<JTerm> termList = extractTermListForPredicate(pm, poVars, d.hasMby);
        final Sort[] argSorts = generateContApplArgumentSorts(termList, pm);
        final Function contApplPred =
            generateContApplPredicate(nameString, argSorts, d.tb, d.services);
        return instantiateContApplPredicate(contApplPred, termList, d.tb);
    }

    protected Sort[] generateContApplArgumentSorts(ImmutableList<JTerm> termList,
            IProgramMethod pm) {

        Sort[] argSorts = new Sort[termList.size()];
        // ImmutableArray<Sort> pmSorts = pm.argSorts();

        int i = 0;
        for (final JTerm arg : termList) {
            argSorts[i] = arg.sort();
            i++;
        }

        return argSorts;
    }


    private Function generateContApplPredicate(String nameString, Sort[] argSorts,
            TermBuilder tb,
            Services services) {
        final Name name = new Name(nameString);
        Namespace<Function> functionNS = services.getNamespaces().functions();

        /*
         * This predicate needs to present on all branches and, therefore, must be added to the
         * toplevel function namespace. Hence, we rewind to the parent namespace here.
         */
        while (functionNS.parent() != null) {
            functionNS = functionNS.parent();
        }

        Function pred = functionNS.lookup(name);

        if (pred == null) {
            pred = new JFunction(name, JavaDLTheory.FORMULA, argSorts);
            functionNS.addSafely(pred);
        }
        return pred;
    }


    private JTerm instantiateContApplPredicate(Function pred, ImmutableList<JTerm> termList,
            TermBuilder tb) {
        final Sort[] predArgSorts = new Sort[pred.argSorts().size()];
        pred.argSorts().toArray(predArgSorts);
        JTerm[] predArgs = new JTerm[predArgSorts.length];

        int i = 0;
        for (final JTerm arg : termList) {
            predArgs[i] = arg;
            i++;
        }

        return tb.func(pred, predArgs);
    }


    abstract String generatePredicateName(IProgramMethod pm, StatementBlock block,
            LoopSpecification loopInv);


    /**
     * Parameters and the result of a method only have to appear once in the predicate. This method
     * chooses the right variables out of the poVars.
     *
     * @param poVars The proof obligation variables.
     * @return
     */
    private ImmutableList<JTerm> extractTermListForPredicate(IProgramMethod pm,
            ProofObligationVars poVars, boolean hasMby) {
        ImmutableList<JTerm> relevantPreVars = ImmutableSLList.nil();
        ImmutableList<JTerm> relevantPostVars = ImmutableSLList.nil();

        if (!pm.isStatic()) {
            // self is relevant in the pre and post state for constructors
            // (if the method is static, then there is no self)
            relevantPreVars = relevantPreVars.append(poVars.pre.self);
            relevantPostVars = relevantPostVars.append(poVars.post.self);
        }

        // local variables which are not changed during execution or whose
        // changes are not observable (like for parameters) are relevant only
        // in the pre state
        Iterator<JTerm> localPostVarsIt = poVars.post.localVars.iterator();
        for (JTerm localPreVar : poVars.pre.localVars) {
            JTerm localPostVar = localPostVarsIt.next();
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
