package recoder.testsuite.basic;

import org.junit.Ignore;
import org.junit.Test;

import static org.junit.Assert.fail;
import static recoder.testsuite.basic.BasicTestsSuite.getConfig;

@Ignore
public class SetupModelTest {
    @Test
    public void testSetupModel() {
        if (getConfig().getProjectSettings().ensureSystemClassesAreInPath()) {
            getConfig().getChangeHistory().updateModel();
        } else {
            fail("Problem with system setup: Cannot locate system classes");
        }
    }
}
