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

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class InfFlowPostSnippet extends ReplaceAnRegisterMethod implements InfFlowFactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars1,
                        ProofObligationVars poVars2)
            throws UnsupportedOperationException {

        // get respects terms
        if (d.getContractContent(BasicSnippetData.Key.RESPECTS) == null) {
            throw new UnsupportedOperationException("Tried to produce "
                    + "respects for a contract without respects.");
        }
        assert Term[][].class.equals(BasicSnippetData.Key.RESPECTS.getType());
        Term[][] origRespects = (Term[][]) d.getContractContent(
                BasicSnippetData.Key.RESPECTS);

        // the respects-sequents evaluated in the pre-state
        Term[][] respectsAtPre1 = replace(origRespects, d.origVars, poVars1);
        Term[][] respectsAtPre2 = replace(origRespects, d.origVars, poVars2);
        // the respects-sequents evaluated in the post-state
        Term[][] respectsAtPost1 = replace(respectsAtPre1,
                                           new Term[]{poVars1.heap,
                    poVars1.self,
                    poVars1.exception},
                                           new Term[]{poVars1.heapAtPost,
                    poVars1.selfAtPost,
                    poVars1.exceptionAtPost});
        Term[][] respectsAtPost2 = replace(respectsAtPre2,
                                           new Term[]{poVars2.heap,
                    poVars2.self,
                    poVars2.exception},
                                           new Term[]{poVars2.heapAtPost,
                    poVars2.selfAtPost,
                    poVars2.exceptionAtPost});

        // get declassifies terms
        if (d.getContractContent(BasicSnippetData.Key.DECLASSIFIES) == null) {
            throw new UnsupportedOperationException("Tried to produce "
                    + "declassifies for a contract without declassifies.");
        }
        assert Term[][].class.equals(BasicSnippetData.Key.DECLASSIFIES.getType());
        Term[][] origDeclassifies = (Term[][]) d.getContractContent(
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
                                          Term[] respectsAtPre1,
                                          Term[] respectsAtPre2,
                                          Term[] respectsAtPost1,
                                          Term[] respectsAtPost2,
                                          Term[][] declassClause1,
                                          Term[][] declassClause2) {
        Term inputRelation =
                buildInputRelation(d, vs1, vs2, respectsAtPre1,
                                   respectsAtPre2, declassClause1,
                                   declassClause2);
        Term outputRelation =
                buildOutputRelation(d, vs1, vs2, respectsAtPost1,
                                    respectsAtPost2);

        return d.tb.imp(inputRelation, outputRelation);
    }

    private Term buildInputRelation(BasicSnippetData d,
                                    ProofObligationVars vs1,
                                    ProofObligationVars vs2,
                                    Term[] referenceLocSet1,
                                    Term[] referenceLocSet2,
                                    Term[][] declassClause1,
                                    Term[][] declassClause2) {
        final Term mainInputEqRelation =
                buildMainInputEqualsRelation(d, vs1, vs2, referenceLocSet1,
                                             referenceLocSet2);
        final Term[] declassifiesRelations =
                buildDeclassifiesRelations(d, referenceLocSet1, declassClause1,
                                           referenceLocSet2, declassClause2);

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
        BasicPOSnippetFactory f1 = POSinppetFactory.getBasicFactory(d, vs1);
        BasicPOSnippetFactory f2 = POSinppetFactory.getBasicFactory(d, vs2);
        Term framingLocs1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_DEP);
        Term framingLocs2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_DEP);

        Term[] eqAtLocs = new Term[respects1.length];
        for (int i = 0; i < eqAtLocs.length; i++) {
            SearchVisitor search = new SearchVisitor(vs1.resultsAtPost.head());
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
            Term[] referenceLocSet1,
            Term[][] declassClause1,
            Term[] referenceLocSet2,
            Term[][] declassClause2) {
        final Term[] declassifications = new Term[declassClause1.length];
        for (int i = 0; i < declassifications.length; i++) {
            declassifications[i] =
                    buildDeclassifiesRelation(d, referenceLocSet1,
                                              declassClause1[i],
                                              referenceLocSet2,
                                              declassClause2[i]);
        }
        return declassifications;
    }

    private Term buildDeclassifiesRelation(
            BasicSnippetData d,
            Term[] referenceLocSet1,
            Term[] declassClause1,
            Term[] referenceLocSet2,
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
                    d.tb.equals(to1, d.tb.seq(referenceLocSet1)),
                    d.tb.equals(to2, d.tb.seq(referenceLocSet2)),
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
                                     Term[] referenceLocSet1,
                                     Term[] referenceLocSet2) {
        Term mainEqRelation =
                buildMainOutputEqualsRelation(d, vs1, vs2, referenceLocSet1,
                                              referenceLocSet2);
        ImmutableList<Term> outputRelations = ImmutableSLList.<Term>nil();
        outputRelations = outputRelations.append(mainEqRelation);
        return d.tb.and(outputRelations);
    }

    private static Term buildMainOutputEqualsRelation(BasicSnippetData d,
                                                      ProofObligationVars vs1,
                                                      ProofObligationVars vs2,
                                                      Term[] referenceLocSet1,
                                                      Term[] referenceLocSet2) {
        BasicPOSnippetFactory f1 = POSinppetFactory.getBasicFactory(d, vs1);
        BasicPOSnippetFactory f2 = POSinppetFactory.getBasicFactory(d, vs2);
        Term framingLocs1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_MOD);
        Term framingLocs2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_MOD);

        Term[] eqAtLocs = new Term[referenceLocSet1.length];
        for (int i = 0; i < eqAtLocs.length; i++) {
            eqAtLocs[i] = d.tb.equals(referenceLocSet1[i], referenceLocSet2[i]);
        }
        return d.tb.and(eqAtLocs);
    }

    private static class SearchVisitor extends Visitor {

        private boolean termFound = false;
        private Term searchTerm;

        public SearchVisitor(Term searchTerm) {
            this.searchTerm = searchTerm;
        }

        public boolean containsTerm() {
            return termFound;
        }

        @Override
        public void visit(Term visited) {
            termFound = termFound || visited.equals(searchTerm);
        }
    }
}
