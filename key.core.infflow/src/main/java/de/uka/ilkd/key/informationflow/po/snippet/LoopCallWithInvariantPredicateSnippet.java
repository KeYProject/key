/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class LoopCallWithInvariantPredicateSnippet extends TwoStateMethodPredicateSnippet {

    @Override
    String generatePredicateName(@Nullable IProgramMethod pm, @Nullable StatementBlock block,
            @Nullable LoopSpecification loopInv) {
        final LoopSpecification loop = requireLoopInv(loopInv);
        final IProgramMethod method = requirePm(pm);
        final String nameString = MiscTools.toValidTacletName(
            "EXECUTION_OF_LOOP_" + "at_line_" + loop.getLoop().getStartPosition().line()
                + "_in_" + method.getUniqueName() + "_WITH_INV").toString();
        return nameString;
    }
}
