package de.uka.ilkd.key;

import de.uka.ilkd.key.nparser.ParsingFacade;
import org.junit.jupiter.api.RepeatedTest;

import java.io.IOException;
import java.nio.file.Paths;

/**
 * @author Alexander Weigl
 * @version 1 (7/21/25)
 */
public class BenchmarkKeYParser {
    @RepeatedTest(value = 50, failureThreshold = 1)
    public void testParse() throws IOException {
        ParsingFacade.parseFile(Paths.get("../all.key"));
    }
}
