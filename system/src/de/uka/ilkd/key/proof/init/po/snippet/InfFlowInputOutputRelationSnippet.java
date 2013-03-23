/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
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
        ProofObligationVars p1 = new ProofObligationVars(poVars1.self,
                                                         poVars1.selfAtPost,
                                                         poVars1.guard,
                                                         poVars1.localIns,
                                                         poVars1.guardAtPost,
                                                         !poVars1.localOuts.isEmpty() ?
                                                                 poVars1.localIns :
                                                                     ImmutableSLList.<Term>nil(),
                                                         poVars1.result,
                                                         poVars1.resultAtPost,
                                                         poVars1.exception,
                                                         poVars1.exceptionAtPost,
                                                         poVars1.heap,
                                                         poVars1.heapAtPre,
                                                         poVars1.heapAtPost,
                                                         poVars1.mbyAtPre,
                                                         poVars1.postfix,
                                                         d.tb.getServices(),
                                                         poVars1.local);
        Triple<Term[],Term[],Term[]>[] respectsAtPre1 = replace(origRespects, d.origVars, p1);

        ProofObligationVars p2 = new ProofObligationVars(poVars2.self,
                                                         poVars2.selfAtPost,
                                                         poVars2.guard,
                                                         poVars2.localIns,
                                                         poVars2.guardAtPost,
                                                         !poVars2.localOuts.isEmpty() ?
                                                                 poVars2.localIns :
                                                                     ImmutableSLList.<Term>nil(),
                                                                     poVars2.result,
                                                                     poVars2.resultAtPost,
                                                                     poVars2.exception,
                                                                     poVars2.exceptionAtPost,
                                                                     poVars2.heap,
                                                                     poVars2.heapAtPre,
                                                                     poVars2.heapAtPost,
                                                                     poVars2.mbyAtPre,
                                                                     poVars2.postfix,
                                                                     d.tb.getServices(),
                                                                     poVars2.local);
        Triple<Term[],Term[],Term[]>[] respectsAtPre2 = replace(origRespects, d.origVars, p2);
        // the respects-sequents evaluated in the post-state
        Term[] pv = new Term[] {poVars1.heap,
                                poVars1.self,
                                poVars1.guard,
                                poVars1.result,
                                poVars1.exception};
        Term[] pre = new Term[pv.length + poVars1.localOuts.size()];
        int p;
        for (p = 0; p < pv.length; p++) {
            pre[p] = pv[p];
        }
        for (Iterator<Term> ins1 = poVars1.localIns.iterator(); p < pre.length; p++) {
            pre[p] = ins1.next();
        }
        pv = new Term[] {poVars1.heapAtPost,
                         poVars1.selfAtPost,
                         poVars1.guardAtPost,
                         poVars1.resultAtPost,
                         poVars1.exceptionAtPost};
        Term[] post = new Term[pv.length + poVars1.localOuts.size()];
        for (p = 0; p < pv.length; p++) {
            post[p] = pv[p];
        }
        for (Iterator<Term> outs1 = poVars1.localOuts.iterator(); p < post.length; p++) {
            post[p] = outs1.next();
        }
        Triple<Term[],Term[],Term[]>[] respectsAtPost1 = replace(respectsAtPre1, pre, post);

        pv = new Term[] {poVars2.heap,
                         poVars2.self,
                         poVars2.guard,
                         poVars2.result,
                         poVars2.exception};
        pre = new Term[pv.length + poVars2.localOuts.size()];
        for (p = 0; p < pv.length; p++) {
            pre[p] = pv[p];
        }
        for (Iterator<Term> ins2 = poVars2.localIns.iterator(); p < pre.length; p++) {
            pre[p] = ins2.next();
        }
        pv = new Term[] {poVars2.heapAtPost,
                         poVars2.selfAtPost,
                         poVars2.guardAtPost,
                         poVars2.resultAtPost,
                         poVars2.exceptionAtPost};
        post = new Term[pv.length + poVars2.localOuts.size()];
        for (p = 0; p < pv.length; p++) {
            post[p] = pv[p];
        }
        for (Iterator<Term> outs2 = poVars2.localOuts.iterator(); p < post.length; p++) {
            post[p] = outs2.next();
        }
        Triple<Term[],Term[],Term[]>[]
                respectsAtPost2 = replace(respectsAtPre2, pre, post);

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
            SearchVisitor search = new SearchVisitor(vs1.result, vs1.resultAtPost);
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
            SearchVisitor search = new SearchVisitor(vs1.result, vs1.resultAtPost);
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

    private static class SearchVisitor extends Visitor {

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
