/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.ImmutableList;

/// Expands a statement into the statements of its block. Non-block statements are returned
/// unchanged. This lets a taclet splice a branch body into a surrounding block without introducing
/// an additional block level, regardless of whether the branch was written with braces.
@TransformerMeta(name = "#blockBody")
public final class BlockBody extends ProgramTransformer {

    public BlockBody(ProgramElement body) {
        super("#blockBody", body);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        if (pe instanceof StatementBlock block) {
            var statements = block.getBody();
            var result = new ProgramElement[statements.size()];
            for (int i = 0; i < statements.size(); i++) {
                result[i] = statements.get(i);
            }
            return result;
        }
        return new ProgramElement[] { pe };
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(body());
    }
}
