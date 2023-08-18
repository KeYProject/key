/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

public class Unpack extends ProgramTransformer {

    /**
     * creates a typeof ProgramTransformer
     *
     * @param loop the instance of expression contained by the meta construct
     */
    public Unpack(For loop) {
        super("unpack", loop);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        Debug.assertTrue(pe instanceof For, "Unpack cannot handle ", pe);
        final For astFor = (For) pe;
        final Statement[] loopInitStatementList =
            new Statement[astFor.getInitializers().size() + 1];
        for (int i = 0; i < loopInitStatementList.length - 1; i++) {
            loopInitStatementList[i] = astFor.getInitializers().get(i);
        }

        loopInitStatementList[loopInitStatementList.length - 1] =
            KeYJavaASTFactory.forLoop(astFor.getGuard(), astFor.getIForUpdates(), astFor.getBody());
        return new ProgramElement[] { KeYJavaASTFactory.block(loopInitStatementList) };
    }
}
