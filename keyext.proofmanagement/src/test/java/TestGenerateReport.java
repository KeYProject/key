import org.junit.jupiter.api.Test;
import org.key_project.proofmanagement.Main;
import org.key_project.proofmanagement.check.CheckerData;
import org.key_project.proofmanagement.io.HTMLReport;
import org.key_project.proofmanagement.io.LogLevel;

import java.io.IOException;
import java.nio.file.Files;

/**
 * @author Alexander Weigl
 * @version 1 (6/16/25)
 */
public class TestGenerateReport {
    @Test void test() throws IOException {
        CheckerData data = new CheckerData(LogLevel.DEBUG);
        HTMLReport.print(data, Files.createTempFile("report", ".html"));
    }
}
