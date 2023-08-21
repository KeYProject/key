/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;


import java.util.Iterator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

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
            InfFlowSpec infFlowSpec2, BasicSnippetData d, ProofObligationVars vs1,
            ProofObligationVars vs2, Term eqAtLocsTerm) {
        // build equalities for newObjects terms
        ImmutableList<Term> newObjEqs = ImmutableSLList.nil();
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
