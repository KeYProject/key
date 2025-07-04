/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;


/**
 * Generate term "self != null".
 * <p/>
 *
 * @author christoph
 */
class MethodCallPredicateSnippet extends TwoStateMethodPredicateSnippet {

    @Override
    String generatePredicateName(IProgramMethod pm, StatementBlock block,
            LoopSpecification loopInv) {
        final String nameString =
            MiscTools.toValidTacletName("RELATED_BY_" + pm.getUniqueName()).toString();
        return nameString;
    }

    @Override
    protected Sort[] generateContApplArgumentSorts(ImmutableList<JTerm> termList,
            IProgramMethod pm) {

        Sort[] argSorts = new Sort[termList.size()];
        ImmutableArray<Sort> pmSorts = pm.argSorts();

        int i = 0;
        for (final JTerm arg : termList) {
            // bugfix: Take the first argument sorts from the definition of
            // the method rather than from the actually provided arguments.
            // aug 2015 SG + MU
            if (i < pmSorts.size() - 1) {
                argSorts[i] = pmSorts.get(i + 1);
            } else {
                argSorts[i] = arg.sort();
            }
            i++;
        }

        return argSorts;
    }
}
