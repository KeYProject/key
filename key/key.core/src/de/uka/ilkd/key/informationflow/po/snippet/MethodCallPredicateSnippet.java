/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.po.snippet;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.MiscTools;


/**
 * Generate term "self != null".
 * <p/>
 * @author christoph
 */
class MethodCallPredicateSnippet extends TwoStateMethodPredicateSnippet {

    @Override
    String generatePredicateName(IProgramMethod pm,
                                 StatementBlock block,
                                 LoopInvariant loopInv) {
        final String nameString =
                MiscTools.toValidTacletName("RELATED_BY_" + pm.getUniqueName()).toString();
        return nameString;
    }

    @Override
    protected Sort[] generateContApplArgumentSorts(
            ImmutableList<Term> termList, IProgramMethod pm) {

        Sort[] argSorts = new Sort[termList.size()];
        ImmutableArray<Sort> pmSorts = pm.argSorts();

        int i = 0;
        for (final Term arg : termList) {
            // bugfix: Take the first argument sorts from the definition of
            // the method rather than from the actually provided arguments.
            // aug 2015 SG + MU
            if(i < pmSorts.size() - 1) {
                argSorts[i] = pmSorts.get(i+1);
            } else {
                argSorts[i] = arg.sort();
            }
            i++;
        }

        return argSorts;
    }
}