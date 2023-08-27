/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic.syntax;

import java.util.List;

import junit.framework.Assert;
import junit.framework.TestCase;
import recoder.convenience.Format;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.SourceElement.Position;
import recoder.testsuite.basic.BasicTestsSuite;

public class WalkPositionTest extends TestCase {

    public void testWalkPosition() {
        SourceFileRepository sfr = BasicTestsSuite.getConfig().getSourceFileRepository();
        List<CompilationUnit> units = sfr.getCompilationUnits();
        for (CompilationUnit u : units) {
            ProgramElement oldPe = u;
            Position oldPos = u.getFirstElement().getStartPosition();
            TreeWalker tw = new TreeWalker(u);
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                Position newPos = pe.getFirstElement().getStartPosition();
                if (newPos.equals(Position.UNDEFINED)) {
                    System.err
                            .println("Position undefined: " + Format.toString("%c @%p in %u", pe));
                }
                if (newPos.getLine() < oldPos.getLine() || (newPos.getLine() == oldPos.getLine()
                        && newPos.getColumn() < newPos.getColumn())) {
                    Assert.fail("Position mismatch: " + Format.toString("%c @%p in %u", oldPe) + "/"
                        + Format.toString("%c @%p", pe));
                }
                oldPos = newPos;
                oldPe = pe;
            }
        }
    }
}
