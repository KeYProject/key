/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.rule.InfFlowTaclet;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.TacletApplPart;


public class InfFlowTacletBuilder extends RewriteTacletBuilder {

    public InfFlowTacletBuilder() {
    }


    @Override
    public RewriteTaclet getRewriteTaclet() {
        if (find == null) {
            throw new TacletBuilder.TacletBuilderException(this, "No find part specified");

        }
        checkBoundInIfAndFind();
        TacletPrefixBuilder prefixBuilder = new TacletPrefixBuilder(this);
        prefixBuilder.build();
        return new InfFlowTaclet(name,
                                 new TacletApplPart(ifseq,
                                                    varsNew,
                                                    varsNotFreeIn,
                                                    varsNewDependingOn,
                                                    variableConditions),
                                 goals, ruleSets,
                                 attrs,
                                 find,
                                 prefixBuilder.getPrefixMap(),
                                 applicationRestriction,
                                 choices,
                                 surviveSmbExec);

    }
}