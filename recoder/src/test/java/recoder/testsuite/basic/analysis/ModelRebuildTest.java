/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic.analysis;

import java.util.List;

import junit.framework.Assert;
import org.junit.Ignore;
import org.junit.Test;
import recoder.abstraction.ClassType;
import recoder.java.CompilationUnit;
import recoder.java.declaration.TypeDeclaration;
import recoder.kit.ProblemReport;
import recoder.kit.Transformation;
import recoder.service.ChangeHistory;
import recoder.testsuite.basic.BasicTestsSuite;

/**
 * Erases all compilation units, checks if the model is "empty", undoes the change and checks if the
 * model report is still valid.
 *
 * @author AL
 * @since 0.72
 */
@Ignore
public class ModelRebuildTest extends AnalysisReportTest {

    @Test
    public void runTest() throws java.io.IOException {
        Transformation clearAll = new Transformation(BasicTestsSuite.getConfig()) {
            public ProblemReport execute() {
                getChangeHistory().begin(this);
                List<CompilationUnit> units = getSourceFileRepository().getCompilationUnits();
                for (CompilationUnit unit : units) {
                    detach(unit);
                }
                return NO_PROBLEM;
            }
        };

        clearAll.execute();
        ChangeHistory ch = BasicTestsSuite.getConfig().getChangeHistory();
        ch.updateModel();

        // model should be cleared now except for byte code and implicitly
        // defined stuff
        Assert.assertEquals(
            BasicTestsSuite.getConfig().getSourceFileRepository().getKnownCompilationUnits().size(),
            0);
        List<ClassType> ctl = BasicTestsSuite.getConfig().getNameInfo().getClassTypes();
        for (int i = ctl.size() - 1; i >= 0; i -= 1) {
            Assert.assertFalse("Syntax tree left in an emptied model",
                ctl.get(i) instanceof TypeDeclaration);
        }

        ch.rollback(clearAll);
        // all units should be registered again now;
        // we do not rollback everything as the initial setup would be
        // rolled back, too

        ch.updateModel();
        // model should be rebuilt now
        super.testAnalysisReport(); // see if the rebuilt model is correct
    }
}
