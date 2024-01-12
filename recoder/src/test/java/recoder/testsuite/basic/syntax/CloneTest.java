/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic.syntax;

import java.util.List;

import junit.framework.Assert;
import junit.framework.TestCase;
import recoder.ProgramFactory;
import recoder.convenience.Format;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.testsuite.basic.BasicTestsSuite;

public class CloneTest extends TestCase {

    public void testClone() {
        SourceFileRepository sfr = BasicTestsSuite.getConfig().getSourceFileRepository();
        ProgramFactory pf = BasicTestsSuite.getConfig().getProgramFactory();
        List<CompilationUnit> units = sfr.getCompilationUnits();
        for (CompilationUnit cu : units) {
            String buffer1 = cu.toSource();
            CompilationUnit cv = cu.deepClone();
            if (!ProgramElement.STRUCTURAL_EQUALITY.equals(cu, cv)) {
                Assert.fail(
                    "Printed tree of " + Format.toString("%u", cu) + " has changed its structure");
            }
            String buffer2 = cv.toSource();
            if (!buffer1.equals(buffer2)) {
                Assert.fail(Format.toString("Reprint of parsed %u differs", cu));
            }
        }
    }
}
