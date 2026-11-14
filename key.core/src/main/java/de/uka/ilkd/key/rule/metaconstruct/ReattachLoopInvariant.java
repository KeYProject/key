/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * Construct for re-attaching a loop invariant that otherwise would get lost after a
 * transformation, for instance, the loop scope-based unwinding rule or the block-elimination
 * taclets (which rebuild the loop node from the taclet pattern). The invariant is taken from the
 * loop that is the active statement of the match context, so the taclet must match the loop it
 * re-builds as the active statement. Copied from the 2015 TimSort tweaks branch (by DS), original
 * work by Richard. Changed extraction of active statement to also work with labeled loops.
 *
 * @author Richard Bubel
 */
public class ReattachLoopInvariant extends ProgramTransformer {
    public ReattachLoopInvariant(LoopStatement ls) {
        super("#reattachLoopInvariant", ls);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        final ProgramElement context = //
            svInst.getContextInstantiation().program();

        if (context != null) {
            final Statement activeStmt =
                (Statement) JavaTools.getActiveStatement(JavaBlock.createJavaBlock(
                    (StatementBlock) svInst.getContextInstantiation().program()));
            assert activeStmt instanceof LoopStatement;

            final LoopStatement loop = (LoopStatement) activeStmt;

            LoopSpecification li = loop.getLoopInvariant();

            if (li != null) {
                li = li.setLoop((LoopStatement) pe);
                ((LoopStatement) pe).setLoopInvariant(li);
            }
        }

        return new ProgramElement[] { pe };
    }
}
