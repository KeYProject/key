/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.Triple;

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
        if (d.get(BasicSnippetData.Key.RESPECTS) == null) {
            throw new UnsupportedOperationException("Tried to produce "
                    + "respects for a contract without respects.");
        }
        assert ImmutableList.class.equals(BasicSnippetData.Key.RESPECTS.getType());
        ImmutableList<Triple<ImmutableList<Term>,ImmutableList<Term>,ImmutableList<Term>>>
            origRespects =
                (ImmutableList<Triple<ImmutableList<Term>,
                 ImmutableList<Term>,ImmutableList<Term>>>) d.get(BasicSnippetData.Key.RESPECTS);

        // the respects-sequents evaluated in the pre-state
        Triple<Term[],Term[],Term[]>[] respectsAtPre1 = replace(origRespects, d.origVars, poVars1.pre);
        Triple<Term[],Term[],Term[]>[] respectsAtPre2 = replace(origRespects, d.origVars, poVars2.pre);

        // the respects-sequents evaluated in the post-state
        Triple<Term[],Term[],Term[]>[] respectsAtPost1 = replace(origRespects, d.origVars, poVars1.post);
        Triple<Term[],Term[],Term[]>[] respectsAtPost2 = replace(origRespects, d.origVars, poVars2.post);

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
                                          Triple<Term[],Term[],Term[]> respectsAtPre1,
                                          Triple<Term[],Term[],Term[]> respectsAtPre2,
                                          Triple<Term[],Term[],Term[]> respectsAtPost1,
                                          Triple<Term[],Term[],Term[]> respectsAtPost2) {
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
                                    Triple<Term[],Term[],Term[]> respects1,
                                    Triple<Term[],Term[],Term[]> respects2) {
        //      BasicPOSnippetFactory f1 = POSnippetFactory.getBasicFactory(d, vs1);
        //      BasicPOSnippetFactory f2 = POSnippetFactory.getBasicFactory(d, vs2);
        //      Term framingLocs1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_DEP);
        //      Term framingLocs2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_DEP);
        Term[] eqAtLocs =
                new Term[respects1.first.length +
                         respects1.second.length];        

        for (int i = 0; i < respects1.first.length; i++) {
            SearchVisitor search = new SearchVisitor(vs1.pre.result, vs1.post.result);
            respects1.first[i].execPreOrder(search);
            if (!search.termFound) {
                // refLocTerms which contain \result are not included in
                // the precondition
                eqAtLocs[i] = d.tb.equals(respects1.first[i], respects2.first[i]);
            } else {
                eqAtLocs[i] = d.tb.tt();
            }
        }
        for (int i = 0; i < respects1.second.length; i++) {
            SearchVisitor search = new SearchVisitor(vs1.pre.result, vs1.post.result);
            respects1.second[i].execPreOrder(search);
            if (!search.termFound) {
                // refLocTerms which contain \result are not included in
                // the precondition
                eqAtLocs[i + respects1.first.length] =
                        d.tb.equals(respects1.second[i], respects2.second[i]);
            } else {
                eqAtLocs[i + respects1.first.length] = d.tb.tt();
            }
        }

        return d.tb.and(eqAtLocs);
    }

    private Term buildOutputRelation(BasicSnippetData d,
                                     ProofObligationVars vs1,
                                     ProofObligationVars vs2,
                                     Triple<Term[],Term[],Term[]> respects1,
                                     Triple<Term[],Term[],Term[]> respects2) {
        //        BasicPOSnippetFactory f1 = POSnippetFactory.getBasicFactory(d, vs1);
        //        BasicPOSnippetFactory f2 = POSnippetFactory.getBasicFactory(d, vs2);
        //        Term framingLocs1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_MOD);
        //        Term framingLocs2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_MOD);

        Term[] eqAtLocs = new Term[respects1.first.length +
                                   respects1.third.length];
        for (int i = 0; i < respects1.first.length; i++) {
            eqAtLocs[i] = d.tb.equals(respects1.first[i], respects2.first[i]);
        }
        for (int i = 0; i < respects1.third.length; i++) {
            eqAtLocs[i + respects1.first.length] =
                    d.tb.equals(respects1.third[i], respects2.third[i]);
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
