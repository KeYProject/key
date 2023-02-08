/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.testsuite.basic.analysis;

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

import java.util.List;

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
