/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic.analysis;

import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import recoder.abstraction.Field;
import recoder.abstraction.Variable;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.reference.VariableReference;
import recoder.service.CrossReferenceSourceInfo;
import recoder.testsuite.basic.BasicTestsSuite;

public class LocalVariableXReferenceCompletenessTest extends XReferenceCompletenessTest {
    @Test
    public void testLocalVariableXReferenceCompletenessTest() {
        CrossReferenceSourceInfo xrsi = BasicTestsSuite.getConfig().getCrossReferenceSourceInfo();
        SourceFileRepository sfr = BasicTestsSuite.getConfig().getSourceFileRepository();

        List<CompilationUnit> units = sfr.getCompilationUnits();
        for (CompilationUnit u : units) {
            TreeWalker tw = new TreeWalker(u);
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                if ((pe instanceof Variable) && !(pe instanceof Field)) {
                    Variable x = (Variable) pe;
                    List<? extends VariableReference> list = xrsi.getReferences(x);
                    for (VariableReference r : list) {
                        Variable y = xrsi.getVariable(r);
                        if (x != y) {
                            Assert.fail(makeResolutionError(r, x, y));
                        }
                    }
                }
            }
        }
    }
}
