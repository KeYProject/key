/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Objects;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.LoopInitializer;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.statement.For;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;

@TransformerMeta(name = "#unpack")
@NullMarked
public class Unpack extends ProgramTransformer {

    /**
     * creates a typeof ProgramTransformer
     *
     * @param loop
     *        the instance of expression contained by the meta construct
     */
    public Unpack(For loop) {
        super("#unpack", loop);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        Debug.assertTrue(pe instanceof For, "Unpack cannot handle ", pe);
        final For astFor = (For) pe;
        final ImmutableArray<LoopInitializer> initializers = Objects.requireNonNull(
            astFor.getInitializers(), "no initializers for unpacked for loop");
        final Statement[] loopInitStatementList = new Statement[initializers.size() + 1];
        for (int i = 0; i < loopInitStatementList.length - 1; i++) {
            loopInitStatementList[i] = initializers.get(i);
        }

        loopInitStatementList[loopInitStatementList.length - 1] =
            KeYJavaASTFactory.forLoop(astFor.getGuard(),
                Objects.requireNonNull(astFor.getIForUpdates(),
                    "no updates for unpacked for loop"),
                astFor.getBody());
        return new ProgramElement[] { KeYJavaASTFactory.block(loopInitStatementList) };
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(body());
    }
}
