package recoder.testsuite.basic.analysis;

import junit.framework.Assert;
import org.junit.Ignore;
import org.junit.Test;
import recoder.abstraction.ClassType;
import recoder.java.CompilationUnit;
import recoder.kit.ProblemReport;
import recoder.kit.Transformation;
import recoder.service.ChangeHistory;
import recoder.testsuite.basic.BasicTestsSuite;

import java.util.List;

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
                for (int i = 0; i < units.size(); i += 1) {
                    detach(units.get(i));
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
            Assert.assertTrue("Syntax tree left in an emptied model",
                !(ctl.get(i) instanceof recoder.java.declaration.TypeDeclaration));
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
