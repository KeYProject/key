/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.SpecificationElement;
import de.uka.ilkd.key.util.MiscTools;

public class LoopCallPredicateSnippet extends TwoStateMethodPredicateSnippet {
    //@Override
    String generatePredicateName(SpecificationElement contract) {
        LoopInvariant inv = (LoopInvariant) contract;
        String nameString =
                MiscTools.toValidTacletName("RELATED_BY_" + inv.getLoop().getBody() +
                        inv.getLoop().getGuardExpression().toString() +
                        inv.getExecutionContext() + inv + "::" + inv.getLoop()
                        + "__LOOP").toString();
        return nameString;
    }
}