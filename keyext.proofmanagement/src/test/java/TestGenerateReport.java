import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.jupiter.api.Test;
import org.key_project.proofmanagement.Main;

import java.io.IOException;
import java.nio.file.Files;

/**
 * @author Alexander Weigl
 * @version 1 (6/16/25)
 */
public class TestGenerateReport {
    @Test
    void test() throws IOException {
        var testDir = HelperClassForTests.TESTCASE_DIRECTORY.resolve("proofBundle")
                .toAbsolutePath().normalize();
        var file = Files.createTempFile("report", ".html");
        Main.check(true, true, true, true, testDir, file);
    }
}
