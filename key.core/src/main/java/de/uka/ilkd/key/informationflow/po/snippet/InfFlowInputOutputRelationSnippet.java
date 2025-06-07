/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;


import java.util.Iterator;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class InfFlowInputOutputRelationSnippet extends ReplaceAndRegisterMethod
        implements InfFlowFactoryMethod {
    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars1,
            ProofObligationVars poVars2) throws UnsupportedOperationException {
        // get information flow specification terms
        if (d.get(BasicSnippetData.Key.INF_FLOW_SPECS) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce " + "information flow relations for a contract without "
                    + "information flow specification.");
        }
        assert ImmutableList.class.equals(BasicSnippetData.Key.INF_FLOW_SPECS.getType());
        @SuppressWarnings("unchecked")
        ImmutableList<InfFlowSpec> origInfFlowSpecs =
            (ImmutableList<InfFlowSpec>) d.get(BasicSnippetData.Key.INF_FLOW_SPECS);

        // the information-flow-specification-sequents evaluated in the pre-state
        InfFlowSpec[] infFlowSpecsAtPre1 = replace(origInfFlowSpecs, d.origVars, poVars1.pre, d.tb);
        InfFlowSpec[] infFlowSpecsAtPre2 = replace(origInfFlowSpecs, d.origVars, poVars2.pre, d.tb);

        // the information-flow-specification-sequents evaluated in the post-state
        InfFlowSpec[] infFlowSpecsAtPost1 =
            replace(origInfFlowSpecs, d.origVars, poVars1.post, d.tb);
        InfFlowSpec[] infFlowSpecsAtPost2 =
            replace(origInfFlowSpecs, d.origVars, poVars2.post, d.tb);

        // create input-output-relations
        final JTerm[] relations = new JTerm[infFlowSpecsAtPre1.length];
        for (int i = 0; i < infFlowSpecsAtPre1.length; i++) {
            relations[i] = buildInputOutputRelation(d, poVars1, poVars2, infFlowSpecsAtPre1[i],
                infFlowSpecsAtPre2[i], infFlowSpecsAtPost1[i], infFlowSpecsAtPost2[i]);
        }

        return d.tb.and(relations);
    }


    private JTerm buildInputOutputRelation(BasicSnippetData d, ProofObligationVars vs1,
            ProofObligationVars vs2, InfFlowSpec infFlowSpecAtPre1, InfFlowSpec infFlowSpecAtPre2,
            InfFlowSpec infFlowSpecAtPost1, InfFlowSpec infFlowSpecAtPost2) {
        JTerm inputRelation = buildInputRelation(d, vs1, vs2, infFlowSpecAtPre1, infFlowSpecAtPre2);
        JTerm outputRelation =
            buildOutputRelation(d, vs1, vs2, infFlowSpecAtPost1, infFlowSpecAtPost2);

        return d.tb.imp(inputRelation,
            d.tb.label(outputRelation, ParameterlessTermLabel.POST_CONDITION_LABEL));
    }


    private JTerm buildInputRelation(BasicSnippetData d, ProofObligationVars vs1,
            ProofObligationVars vs2, InfFlowSpec infFlowSpec1, InfFlowSpec infFlowSpec2) {
        JTerm[] eqAtLocs = new JTerm[infFlowSpec1.preExpressions.size()];

        Iterator<JTerm> preExp1It = infFlowSpec1.preExpressions.iterator();
        Iterator<JTerm> preExp2It = infFlowSpec2.preExpressions.iterator();
        for (int i = 0; i < infFlowSpec1.preExpressions.size(); i++) {
            JTerm preExp1Term = preExp1It.next();
            JTerm preExp2Term = preExp2It.next();
            SearchVisitor search = new SearchVisitor(vs1.pre.result, vs1.post.result);
            preExp1Term.execPreOrder(search);
            if (!search.termFound) {
                eqAtLocs[i] = d.tb.equals(preExp1Term, preExp2Term);
            } else {
                // terms which contain \result are not included in
                // the precondition
                eqAtLocs[i] = d.tb.tt();
            }
        }

        return d.tb.and(eqAtLocs);
    }

    private JTerm buildOutputRelation(BasicSnippetData d, ProofObligationVars vs1,
            ProofObligationVars vs2, InfFlowSpec infFlowSpec1, InfFlowSpec infFlowSpec2) {
        // build equalities for post expressions
        ImmutableList<JTerm> eqAtLocs = ImmutableSLList.nil();

        Iterator<JTerm> postExp1It = infFlowSpec1.postExpressions.iterator();
        Iterator<JTerm> postExp2It = infFlowSpec2.postExpressions.iterator();
        for (int i = 0; i < infFlowSpec1.postExpressions.size(); i++) {
            JTerm postExp1Term = postExp1It.next();
            JTerm postExp2Term = postExp2It.next();
            eqAtLocs = eqAtLocs.append(d.tb.equals(postExp1Term, postExp2Term));
        }
        final JTerm eqAtLocsTerm = d.tb.and(eqAtLocs);

        if (infFlowSpec1.newObjects.isEmpty()) {
            // object insensitive case
            return eqAtLocsTerm;
        } else {
            // object sensitive case
            return buildObjectSensitivePostRelation(infFlowSpec1, infFlowSpec2, d, vs1, vs2,
                eqAtLocsTerm);
        }
    }


    protected JTerm buildObjectSensitivePostRelation(InfFlowSpec infFlowSpec1,
            InfFlowSpec infFlowSpec2, BasicSnippetData d, ProofObligationVars vs1,
            ProofObligationVars vs2, JTerm eqAtLocsTerm) {
        // build equalities for newObjects terms
        ImmutableList<JTerm> newObjEqs = ImmutableSLList.nil();
        Iterator<JTerm> newObjects1It = infFlowSpec1.newObjects.iterator();
        Iterator<JTerm> newObjects2It = infFlowSpec2.newObjects.iterator();
        for (int i = 0; i < infFlowSpec1.newObjects.size(); i++) {
            JTerm newObject1Term = newObjects1It.next();
            JTerm newObject2Term = newObjects2It.next();
            newObjEqs = newObjEqs.append(d.tb.equals(newObject1Term, newObject2Term));
        }
        final JTerm newObjEqsTerm = d.tb.and(newObjEqs);

        // build isomorphism term for newObjects
        final JTerm newObjsSeq1 = d.tb.seq(infFlowSpec1.newObjects);
        final JTerm newObjsSeq2 = d.tb.seq(infFlowSpec2.newObjects);
        final Function newObjectsIso =
            d.services.getNamespaces().functions().lookup("newObjectsIsomorphic");
        final JTerm isoTerm =
            d.tb.func(newObjectsIso, newObjsSeq1, vs1.pre.heap, newObjsSeq2, vs2.pre.heap);

        // build object oriented post-relation (object sensitive case)
        final JTerm ooPostRelation = d.tb.and(isoTerm, d.tb.imp(newObjEqsTerm, eqAtLocsTerm));
        if (vs1.pre.guard != null && vs1.post.guard != null && vs2.pre.guard != null
                && vs2.post.guard != null) {
            // Case of loop invariants.
            // In this case newObjecs is only considered in case the
            // loop body is entered. Otherwise no code is executed an
            // hence also no objects can be created.
            final JTerm preGuardFalse1 = d.tb.equals(vs1.pre.guard, d.tb.FALSE());
            final JTerm preGuardFalse2 = d.tb.equals(vs2.pre.guard, d.tb.FALSE());
            return d.tb.ife(d.tb.and(preGuardFalse1, preGuardFalse2), eqAtLocsTerm, ooPostRelation);
        } else {
            // Normal case.
            return ooPostRelation;
        }
    }


    private static class SearchVisitor implements DefaultVisitor {

        private boolean termFound = false;
        private final JTerm[] searchTerms;

        public SearchVisitor(JTerm... searchTerms) {
            this.searchTerms = searchTerms;
        }

        @Override
        public void visit(Term visited) {
            for (Term searchTerm : searchTerms) {
                termFound = termFound || visited.equals(searchTerm);
            }
        }
    }
}
