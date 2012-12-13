/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.Pair;

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
        ImmutableList<Pair<ImmutableList<Term>,ImmutableList<Term>>> origRespects =
                (ImmutableList<Pair<ImmutableList<Term>,ImmutableList<Term>>>) d.get(BasicSnippetData.Key.RESPECTS);

        // the respects-sequents evaluated in the pre-state
        Pair<Term[],Term[]>[] respectsAtPre1 = replace(origRespects, d.origVars, poVars1);
        Pair<Term[],Term[]>[] respectsAtPre2 = replace(origRespects, d.origVars, poVars2);
        // the respects-sequents evaluated in the post-state
        Pair<Term[],Term[]>[] respectsAtPost1 = replace(respectsAtPre1,
                                           new Term[]{poVars1.heap,
                                                      poVars1.self,
                                                      poVars1.result,
                                                      poVars1.exception},
                                           new Term[]{poVars1.heapAtPost,
                                                      poVars1.selfAtPost,
                                                      poVars1.resultAtPost,
                                                      poVars1.exceptionAtPost});
        Pair<Term[],Term[]>[] respectsAtPost2 = replace(respectsAtPre2,
                                           new Term[]{poVars2.heap,
                                                      poVars2.self,
                                                      poVars2.result,
                                                      poVars2.exception},
                                           new Term[]{poVars2.heapAtPost,
                                                      poVars2.selfAtPost,
                                                      poVars2.resultAtPost,
                                                      poVars2.exceptionAtPost});

        // get declassifies terms
        if (d.get(BasicSnippetData.Key.DECLASSIFIES) == null) {
            throw new UnsupportedOperationException("Tried to produce "
                    + "declassifies for a contract without declassifies.");
        }
        assert Term[][].class.equals(BasicSnippetData.Key.DECLASSIFIES.getType());
        Term[][] origDeclassifies = (Term[][]) d.get(
                BasicSnippetData.Key.DECLASSIFIES);

        // declassifies has only to be evaluated in the pre-state
        Term[][] declassifies1 = replace(origDeclassifies, d.origVars, poVars1);
        Term[][] declassifies2 = replace(origDeclassifies, d.origVars, poVars2);

        // create input-output-relations
        final Term[] relations = new Term[respectsAtPre1.length];
        for (int i = 0; i < respectsAtPre1.length; i++) {
            relations[i] = buildInputOutputRelation(d, poVars1, poVars2,
                                                    respectsAtPre1[i],
                                                    respectsAtPre2[i],
                                                    respectsAtPost1[i],
                                                    respectsAtPost2[i],
                                                    declassifies1,
                                                    declassifies2);
        }

        return d.tb.and(relations);
    }

    private Term buildInputOutputRelation(BasicSnippetData d,
                                          ProofObligationVars vs1,
                                          ProofObligationVars vs2,
                                          Pair<Term[],Term[]> respectsAtPre1,
                                          Pair<Term[],Term[]> respectsAtPre2,
                                          Pair<Term[],Term[]> respectsAtPost1,
                                          Pair<Term[],Term[]> respectsAtPost2,
                                          Term[][] declassClause1,
                                          Term[][] declassClause2) {
        Term[] respectsAtPreTerms1 = (hasDependsOn(respectsAtPre1)) ?
                                     respectsAtPre1.second :
                                     respectsAtPre1.first;
        Term[] respectsAtPreTerms2 = (hasDependsOn(respectsAtPre2)) ?
                                     respectsAtPre2.second :
                                     respectsAtPre2.first;
        Term inputRelation =
                buildInputRelation(d, vs1, vs2, respectsAtPreTerms1,
                                   respectsAtPreTerms2, declassClause1,
                                   declassClause2);
        Term outputRelation =
                buildOutputRelation(d, vs1, vs2, respectsAtPost1.first,
                                    respectsAtPost2.first);

        return d.tb.imp(inputRelation, outputRelation);
    }


    private boolean hasDependsOn(Pair<Term[], Term[]> respectsAtPre1) {
        return respectsAtPre1.second.length > 0;
    }

    private Term buildInputRelation(BasicSnippetData d,
                                    ProofObligationVars vs1,
                                    ProofObligationVars vs2,
                                    Term[] respects1,
                                    Term[] respects2,
                                    Term[][] declassClause1,
                                    Term[][] declassClause2) {
        final Term mainInputEqRelation =
                buildMainInputEqualsRelation(d, vs1, vs2, respects1,
                                             respects2);
        final Term[] declassifiesRelations =
                buildDeclassifiesRelations(d, respects1, declassClause1,
                                           respects2, declassClause2);

        ImmutableList<Term> inputRelations =
                ImmutableSLList.<Term>nil();
        inputRelations = inputRelations.append(mainInputEqRelation);
        inputRelations = inputRelations.append(declassifiesRelations);

        return d.tb.and(inputRelations);
    }

    private Term buildMainInputEqualsRelation(BasicSnippetData d,
                                              ProofObligationVars vs1,
                                              ProofObligationVars vs2,
                                              Term[] respects1,
                                              Term[] respects2) {
//        BasicPOSnippetFactory f1 = POSnippetFactory.getBasicFactory(d, vs1);
//        BasicPOSnippetFactory f2 = POSnippetFactory.getBasicFactory(d, vs2);
//        Term framingLocs1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_DEP);
//        Term framingLocs2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_DEP);

        Term[] eqAtLocs = new Term[respects1.length];
        for (int i = 0; i < eqAtLocs.length; i++) {
            SearchVisitor search = new SearchVisitor(vs1.result, vs1.resultAtPost);
            respects1[i].execPreOrder(search);
            if (!search.termFound) {
                // refLocTerms which contain \result are not included in
                // the precondition
                eqAtLocs[i] = d.tb.equals(respects1[i], respects2[i]);
            } else {
                eqAtLocs[i] = d.tb.tt();
            }
        }
        return d.tb.and(eqAtLocs);
    }

    private Term[] buildDeclassifiesRelations(
            BasicSnippetData d,
            Term[] respects1,
            Term[][] declassClause1,
            Term[] respects2,
            Term[][] declassClause2) {
        final Term[] declassifications = new Term[declassClause1.length];
        for (int i = 0; i < declassifications.length; i++) {
            declassifications[i] =
                    buildDeclassifiesRelation(d, respects1,
                                              declassClause1[i],
                                              respects2,
                                              declassClause2[i]);
        }
        return declassifications;
    }

    private Term buildDeclassifiesRelation(
            BasicSnippetData d,
            Term[] respects1,
            Term[] declassClause1,
            Term[] respects2,
            Term[] declassClause2) {
        final Term declassification1 = declassClause1[0];
        final Term from1 = declassClause1[1];
        final Term to1 = declassClause1[2];
        final Term ifTerm1 = declassClause1[3];

        final Term declassification2 = declassClause2[0];
        final Term from2 = declassClause2[1];
        final Term to2 = declassClause2[2];
        final Term ifTerm2 = declassClause2[3];

        Term eqTerm = d.tb.equals(declassification1, declassification2);

        Term condition = d.tb.tt();
        if (ifTerm1 != null) {
            condition = d.tb.and(ifTerm1, ifTerm2);
        }
        if (to1 != null) {
            condition = d.tb.and(
                    d.tb.equals(to1, d.tb.seq(respects1)),
                    d.tb.equals(to2, d.tb.seq(respects2)),
                    condition);
        }
        if (from1 != null) {
            // TODO: to be implemented
        }

        return d.tb.imp(condition, eqTerm);
    }

    private Term buildOutputRelation(BasicSnippetData d,
                                     ProofObligationVars vs1,
                                     ProofObligationVars vs2,
                                     Term[] respects1,
                                     Term[] respects2) {
        Term mainEqRelation =
                buildMainOutputEqualsRelation(d, vs1, vs2, respects1,
                                              respects2);
        ImmutableList<Term> outputRelations = ImmutableSLList.<Term>nil();
        outputRelations = outputRelations.append(mainEqRelation);
        return d.tb.and(outputRelations);
    }

    private static Term buildMainOutputEqualsRelation(BasicSnippetData d,
                                                      ProofObligationVars vs1,
                                                      ProofObligationVars vs2,
                                                      Term[] respects1,
                                                      Term[] respects2) {
        BasicPOSnippetFactory f1 = POSnippetFactory.getBasicFactory(d, vs1);
        BasicPOSnippetFactory f2 = POSnippetFactory.getBasicFactory(d, vs2);
        Term framingLocs1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_MOD);
        Term framingLocs2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_MOD);

        Term[] eqAtLocs = new Term[respects1.length];
        for (int i = 0; i < eqAtLocs.length; i++) {
            eqAtLocs[i] = d.tb.equals(respects1[i], respects2[i]);
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
