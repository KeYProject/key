/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.Triple;
import java.util.Iterator;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class InfFlowInputOutputRelationSnippet extends ReplaceAndRegisterMethod
    implements InfFlowFactoryMethod {
    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars1,
                        ProofObligationVars poVars2)
            throws UnsupportedOperationException {
        // get respects terms
        if (d.get(BasicSnippetData.Key.INF_FLOW_SPECS) == null) {
            throw new UnsupportedOperationException("Tried to produce " +
                    "information flow relations for a contract without " +
                    "information flow specification.");
        }
        assert ImmutableList.class.equals(BasicSnippetData.Key.INF_FLOW_SPECS.getType());
        ImmutableList<InfFlowSpec>
            origRespects =
                (ImmutableList<InfFlowSpec>) d.get(BasicSnippetData.Key.INF_FLOW_SPECS);

        // the respects-sequents evaluated in the pre-state
        InfFlowSpec[] respectsAtPre1 = replace(origRespects, d.origVars, poVars1.pre);
        InfFlowSpec[] respectsAtPre2 = replace(origRespects, d.origVars, poVars2.pre);

        // the respects-sequents evaluated in the post-state
        InfFlowSpec[] respectsAtPost1 = replace(origRespects, d.origVars, poVars1.post);
        InfFlowSpec[] respectsAtPost2 = replace(origRespects, d.origVars, poVars2.post);

        // create input-output-relations
        final Term[] relations = new Term[respectsAtPre1.length];
        for (int i = 0; i < respectsAtPre1.length; i++) {
            relations[i] = buildInputOutputRelation(d, poVars1, poVars2,
                                                    respectsAtPre1[i],
                                                    respectsAtPre2[i],
                                                    respectsAtPost1[i],
                                                    respectsAtPost2[i]);
        }

        return d.tb.and(relations);
    }


    private Term buildInputOutputRelation(BasicSnippetData d,
                                          ProofObligationVars vs1,
                                          ProofObligationVars vs2,
                                          InfFlowSpec respectsAtPre1,
                                          InfFlowSpec respectsAtPre2,
                                          InfFlowSpec respectsAtPost1,
                                          InfFlowSpec respectsAtPost2) {
        Term inputRelation =
                buildInputRelation(d, vs1, vs2, respectsAtPre1,
                                   respectsAtPre2);
        Term outputRelation =
                buildOutputRelation(d, vs1, vs2, respectsAtPost1,
                                    respectsAtPost2);

        return d.tb.imp(inputRelation, outputRelation);
    }


    private Term buildInputRelation(BasicSnippetData d,
                                    ProofObligationVars vs1,
                                    ProofObligationVars vs2,
                                    InfFlowSpec infFlowSpec1,
                                    InfFlowSpec infFlowSpec2) {
        //      BasicPOSnippetFactory f1 = POSnippetFactory.getBasicFactory(d, vs1);
        //      BasicPOSnippetFactory f2 = POSnippetFactory.getBasicFactory(d, vs2);
        //      Term framingLocs1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_DEP);
        //      Term framingLocs2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_DEP);
        Term[] eqAtLocs =
                new Term[infFlowSpec1.seperates.size() +
                         infFlowSpec1.declassifies.size()];

        Iterator<Term> seperates1It = infFlowSpec1.seperates.iterator();
        Iterator<Term> seperates2It = infFlowSpec2.seperates.iterator();
        for (int i = 0; i < infFlowSpec1.seperates.size(); i++) {
            Term seperates1Term = seperates1It.next();
            Term seperates2Term = seperates2It.next();
            SearchVisitor search = new SearchVisitor(vs1.pre.result, vs1.post.result);
            seperates1Term.execPreOrder(search);
            if (!search.termFound) {
                eqAtLocs[i] = d.tb.equals(seperates1Term, seperates2Term);
            } else {
                // terms which contain \result are not included in
                // the precondition
                eqAtLocs[i] = d.tb.tt();
            }
        }

        Iterator<Term> declassifies1It = infFlowSpec1.declassifies.iterator();
        Iterator<Term> declassifies2It = infFlowSpec2.declassifies.iterator();
        for (int i = 0; i < infFlowSpec1.declassifies.size(); i++) {
            Term declassifies1Term = declassifies1It.next();
            Term declassifies2Term = declassifies2It.next();
            SearchVisitor search = new SearchVisitor(vs1.pre.result, vs1.post.result);
            declassifies1Term.execPreOrder(search);
            if (!search.termFound) {
                eqAtLocs[i + infFlowSpec1.seperates.size()] =
                        d.tb.equals(declassifies1Term, declassifies2Term);
            } else {
                // terms which contain \result are not included in
                // the precondition
                eqAtLocs[i + infFlowSpec1.seperates.size()] = d.tb.tt();
            }
        }

        return d.tb.and(eqAtLocs);
    }

    private Term buildOutputRelation(BasicSnippetData d,
                                     ProofObligationVars vs1,
                                     ProofObligationVars vs2,
                                     InfFlowSpec infFlowSpec1,
                                     InfFlowSpec infFlowSpec2) {
        //        BasicPOSnippetFactory f1 = POSnippetFactory.getBasicFactory(d, vs1);
        //        BasicPOSnippetFactory f2 = POSnippetFactory.getBasicFactory(d, vs2);
        //        Term framingLocs1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_MOD);
        //        Term framingLocs2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_MOD);

        Term[] eqAtLocs = new Term[infFlowSpec1.seperates.size() +
                                   infFlowSpec1.erases.size()];
        Iterator<Term> seperates1It = infFlowSpec1.seperates.iterator();
        Iterator<Term> seperates2It = infFlowSpec2.seperates.iterator();
        for (int i = 0; i < infFlowSpec1.seperates.size(); i++) {
            Term seperates1Term = seperates1It.next();
            Term seperates2Term = seperates2It.next();
            eqAtLocs[i] = d.tb.equals(seperates1Term, seperates2Term);
        }
        Iterator<Term> erases1It = infFlowSpec1.erases.iterator();
        Iterator<Term> erases2It = infFlowSpec2.erases.iterator();
        for (int i = 0; i < infFlowSpec1.erases.size(); i++) {
            Term erases1Term = erases1It.next();
            Term erases2Term = erases2It.next();
            eqAtLocs[i + infFlowSpec1.seperates.size()] =
                    d.tb.equals(erases1Term, erases2Term);
        }

        return d.tb.and(eqAtLocs);
    }

    private static class SearchVisitor extends DefaultVisitor {

        private boolean termFound = false;
        private Term[] searchTerms;

        public SearchVisitor(Term... searchTerms) {
            this.searchTerms = searchTerms;
        }

        public boolean containsTerm() {
            return termFound;
        }

        @Override
        public void visit(Term visited) {
            for (Term searchTerm : searchTerms) {
                termFound = termFound || visited.equals(searchTerm);
            }
        }
    }
}
