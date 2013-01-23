/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.Triple;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class InfFlowInputOutputRelationSnippet extends ReplaceAndRegisterMethod implements InfFlowFactoryMethod {

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
        Triple<Term[],Term[],Term[]>[] respectsAtPre1 = replace(origRespects, d.origVars, poVars1);
        Triple<Term[],Term[],Term[]>[] respectsAtPre2 = replace(origRespects, d.origVars, poVars2);
        // the respects-sequents evaluated in the post-state
        ImmutableList<Term> poVars1Pre =
                poVars1.localIns
                    .prepend(poVars1.heap, poVars1.self, poVars1.guard)
                        .append(poVars1.result, poVars1.exception);
        ImmutableList<Term> poVars1Post =
                poVars1.localOuts
                    .prepend(poVars1.heapAtPost, poVars1.selfAtPost, poVars1.guardAtPost)
                        .append(poVars1.resultAtPost, poVars1.exceptionAtPost);
        ImmutableList<Term> poVars2Pre =
                poVars2.localIns
                    .prepend(poVars2.heap, poVars2.self, poVars2.guard)
                        .append(poVars2.result, poVars2.exception);
        ImmutableList<Term> poVars2Post =
                poVars2.localOuts
                    .prepend(poVars2.heapAtPost, poVars2.selfAtPost, poVars2.guardAtPost)
                        .append(poVars2.resultAtPost, poVars2.exceptionAtPost);
        Term[] pre1 = new Term [poVars1.localIns.size() + 5];        
        Term[] post1 = new Term [poVars1.localOuts.size() + 5];
        Term[] pre2 = new Term [poVars2.localIns.size() + 5];        
        Term[] post2 = new Term [poVars2.localOuts.size() + 5];
        pre1 = poVars1Pre.toArray(pre1);
        post1 = poVars1Pre.toArray(pre1);
        pre2 = poVars1Pre.toArray(pre1);
        post2 = poVars1Pre.toArray(pre1);
        
        /*
        Term[] pre1 = {poVars1.heap, poVars1.self, poVars1.guard, poVars1.result, poVars1.exception};
        Term[] post1 = {poVars1.heapAtPost, poVars1.selfAtPost, poVars1.guardAtPost, poVars1.resultAtPost, poVars1.exceptionAtPost};
        Term[] pre2 = {poVars2.heap, poVars2.self, poVars2.guard, poVars2.result, poVars2.exception};
        Term[] post2 = {poVars2.heapAtPost, poVars2.selfAtPost, poVars2.guardAtPost, poVars2.resultAtPost, poVars2.exceptionAtPost};
        */
        
        Triple<Term[],Term[],Term[]>[] respectsAtPost1 = replace(respectsAtPre1,
                                                                 pre1,
                                                                 post1);
        Triple<Term[],Term[],Term[]>[] respectsAtPost2 = replace(respectsAtPre2,
                                                                 pre2,
                                                                 post2);

/*
        // get declassifies terms
        if (d.get(BasicSnippetData.Key.DECLASSIFIES) == null &&
            d.get(BasicSnippetData.Key.LOOP_INVARIANT) == null) {
            throw new UnsupportedOperationException("Tried to produce "
                    + "declassifies for a contract without declassifies.");            
        }

        Term[][] declassifies1 = null;
        Term[][] declassifies2 = null;

        if (d.get(BasicSnippetData.Key.LOOP_INVARIANT) == null) {
            assert Term[][].class.equals(BasicSnippetData.Key.DECLASSIFIES.getType());
            Term[][] origDeclassifies = (Term[][]) d.get(
                    BasicSnippetData.Key.DECLASSIFIES);
         // declassifies has only to be evaluated in the pre-state
            declassifies1 = replace(origDeclassifies, d.origVars, poVars1);
            declassifies2 = replace(origDeclassifies, d.origVars, poVars2);
        }        
*/
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
        Term[] eqAtLocs = new Term[respects1.first.length + respects1.second.length];
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
                eqAtLocs[i + respects1.first.length] = d.tb.equals(respects1.second[i], respects2.second[i]);
            } else {
                eqAtLocs[i + respects1.first.length] = d.tb.tt();
            }
        }
        Iterator<Term> itIn1 = vs1.localIns.iterator();
        Iterator<Term> itIn2 = vs2.localIns.iterator();
        Term[] eqAtLocalIns = new Term[vs1.localIns.size()];
        int i = 0;
        while (itIn1.hasNext()) {
            eqAtLocalIns[i++] = d.tb.equals(itIn1.next(), itIn2.next());
        }
        Term eqAtGuard = d.tb.tt();
        if (vs1.guard != null) {            
            eqAtGuard = d.tb.equals(vs1.guard, vs2.guard);
        }
        Term[] eqAt = {d.tb.and(eqAtLocs), d.tb.and(eqAtLocalIns), eqAtGuard};
        return d.tb.and(eqAt);
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

        Term[] eqAtLocs = new Term[respects1.first.length + respects1.third.length];
        for (int i = 0; i < respects1.first.length; i++) {
            eqAtLocs[i] = d.tb.equals(respects1.first[i], respects2.first[i]);
        }
        for (int i = 0; i < respects1.third.length; i++) {
            eqAtLocs[i + respects1.first.length] = d.tb.equals(respects1.third[i], respects2.third[i]);
        }
        Iterator<Term> itOut1 = vs1.localOuts.iterator();
        Iterator<Term> itOut2 = vs2.localOuts.iterator();
        Term[] eqAtLocalOuts = new Term[vs1.localOuts.size()];
        int i = 0;
        while (itOut1.hasNext()) {
            eqAtLocalOuts[i++] = d.tb.equals(itOut1.next(), itOut2.next());
        }
        Term eqAtGuard = d.tb.tt();
        if (vs1.guard != null) {            
            eqAtGuard = d.tb.equals(vs1.guardAtPost, vs2.guardAtPost);
        }
        Term[] eqAt = {d.tb.and(eqAtLocs), d.tb.and(eqAtLocalOuts), eqAtGuard};
        return d.tb.and(eqAt);
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
