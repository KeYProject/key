package de.uka.ilkd.key;

import de.uka.ilkd.key.AutoSuite.AutoSuiteExclude;
import de.uka.ilkd.key.AutoSuite.AutoSuitePath;
import org.junit.runner.RunWith;
import org.key_project.util.testcategories.Interactive;
import org.key_project.util.testcategories.Slow;

@RunWith(AutoSuite.class)
@AutoSuitePath("build/classes/java/test/")
@AutoSuiteExclude(
        categories = { Interactive.class, Slow.class }
)
public class FastTests {
}
