/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;
import java.util.Iterator;

/**
 *
 * @author christoph
 */
class InfFlowContractAppInOutRelationSnippet extends InfFlowInputOutputRelationSnippet {

    // In case of the application of an information flow contract we can
    // assume the identity on the newly created objects, as opposed to the
    // proof obligation where we have to show that there is an isomorphism.
    @Override
    protected Term buildObjectSensitivePostRelation(InfFlowSpec infFlowSpec1,
                                                    InfFlowSpec infFlowSpec2,
                                                    BasicSnippetData d,
                                                    ProofObligationVars vs1,
                                                    ProofObligationVars vs2,
                                                    Term eqAtLocsTerm) {
        // build equalities for newObjects terms
        ImmutableList<Term> newObjEqs = ImmutableSLList.<Term>nil();
        Iterator<Term> newObjects1It = infFlowSpec1.newObjects.iterator();
        Iterator<Term> newObjects2It = infFlowSpec2.newObjects.iterator();
        for (int i = 0; i < infFlowSpec1.newObjects.size(); i++) {
            Term newObject1Term = newObjects1It.next();
            Term newObject2Term = newObjects2It.next();
            newObjEqs = newObjEqs.append(d.tb.equals(newObject1Term, newObject2Term));
        }
        final Term newObjEqsTerm = d.tb.and(newObjEqs);

        // build object oriented post-relation for contract applications
        return d.tb.and(eqAtLocsTerm, newObjEqsTerm);
    }

}
