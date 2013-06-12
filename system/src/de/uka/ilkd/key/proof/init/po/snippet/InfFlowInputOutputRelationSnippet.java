/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;
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
        // get information flow specification terms
        if (d.get(BasicSnippetData.Key.INF_FLOW_SPECS) == null) {
            throw new UnsupportedOperationException("Tried to produce " +
                    "information flow relations for a contract without " +
                    "information flow specification.");
        }
        assert ImmutableList.class.equals(BasicSnippetData.Key.INF_FLOW_SPECS.getType());
        ImmutableList<InfFlowSpec>
            origInfFlowSpecs =
                (ImmutableList<InfFlowSpec>) d.get(BasicSnippetData.Key.INF_FLOW_SPECS);

        // the information-flow-specification-sequents evaluated in the pre-state
        InfFlowSpec[] infFlowSpecsAtPre1 = replace(origInfFlowSpecs, d.origVars, poVars1.pre);
        InfFlowSpec[] infFlowSpecsAtPre2 = replace(origInfFlowSpecs, d.origVars, poVars2.pre);

        // the information-flow-specification-sequents evaluated in the post-state
        InfFlowSpec[] infFlowSpecsAtPost1 = replace(origInfFlowSpecs, d.origVars, poVars1.post);
        InfFlowSpec[] infFlowSpecsAtPost2 = replace(origInfFlowSpecs, d.origVars, poVars2.post);

        // create input-output-relations
        final Term[] relations = new Term[infFlowSpecsAtPre1.length];
        for (int i = 0; i < infFlowSpecsAtPre1.length; i++) {
            relations[i] = buildInputOutputRelation(d, poVars1, poVars2,
                                                    infFlowSpecsAtPre1[i],
                                                    infFlowSpecsAtPre2[i],
                                                    infFlowSpecsAtPost1[i],
                                                    infFlowSpecsAtPost2[i]);
        }

        return d.tb.and(relations);
    }


    private Term buildInputOutputRelation(BasicSnippetData d,
                                          ProofObligationVars vs1,
                                          ProofObligationVars vs2,
                                          InfFlowSpec infFlowSpecAtPre1,
                                          InfFlowSpec infFlowSpecAtPre2,
                                          InfFlowSpec infFlowSpecAtPost1,
                                          InfFlowSpec infFlowSpecAtPost2) {
        Term inputRelation =
                buildInputRelation(d, vs1, vs2, infFlowSpecAtPre1,
                                   infFlowSpecAtPre2);
        Term outputRelation =
                buildOutputRelation(d, vs1, vs2, infFlowSpecAtPost1,
                                    infFlowSpecAtPost2);

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
                new Term[infFlowSpec1.separates.size() +
                         infFlowSpec1.declassifies.size()];

        Iterator<Term> separates1It = infFlowSpec1.separates.iterator();
        Iterator<Term> separates2It = infFlowSpec2.separates.iterator();
        for (int i = 0; i < infFlowSpec1.separates.size(); i++) {
            Term separates1Term = separates1It.next();
            Term separates2Term = separates2It.next();
            SearchVisitor search = new SearchVisitor(vs1.pre.result, vs1.post.result);
            separates1Term.execPreOrder(search);
            if (!search.termFound) {
                eqAtLocs[i] = d.tb.equals(separates1Term, separates2Term);
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
                eqAtLocs[i + infFlowSpec1.separates.size()] =
                        d.tb.equals(declassifies1Term, declassifies2Term);
            } else {
                // terms which contain \result are not included in
                // the precondition
                eqAtLocs[i + infFlowSpec1.separates.size()] = d.tb.tt();
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

        ImmutableList<Term> eqAtLocs = ImmutableSLList.<Term>nil();
        Iterator<Term> separates1It = infFlowSpec1.separates.iterator();
        Iterator<Term> separates2It = infFlowSpec2.separates.iterator();
        for (int i = 0; i < infFlowSpec1.separates.size(); i++) {
            Term separates1Term = separates1It.next();
            Term separates2Term = separates2It.next();
            eqAtLocs = eqAtLocs.append(d.tb.equals(separates1Term, separates2Term));
        }

        Iterator<Term> erases1It = infFlowSpec1.erases.iterator();
        Iterator<Term> erases2It = infFlowSpec2.erases.iterator();
        for (int i = 0; i < infFlowSpec1.erases.size(); i++) {
            Term erases1Term = erases1It.next();
            Term erases2Term = erases2It.next();
            eqAtLocs = eqAtLocs.append(d.tb.equals(erases1Term, erases2Term));
        }
        final Term eqAtLocsTerm = d.tb.and(eqAtLocs);

        Term result = eqAtLocsTerm;
        if (!infFlowSpec1.newObjects.isEmpty()) {
            final Term newObjs1 = d.tb.seq(infFlowSpec1.newObjects);
            final Term newObjs2 = d.tb.seq(infFlowSpec2.newObjects);
            final Services services = d.tb.getServices();
            final Function newObjectsIso =
                    (Function)services.getNamespaces().functions().lookup("newObjectsIsomorphic");
            final Term isoTerm = d.tb.func(newObjectsIso, newObjs1, vs1.pre.heap,
                                           newObjs2, vs2.pre.heap);
            result = d.tb.and(isoTerm, d.tb.imp(d.tb.equals(newObjs1, newObjs2), result));
        }

        return result;
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
