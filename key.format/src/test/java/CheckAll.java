import de.uka.ilkd.key.nparser.format.KeyFormatFacade;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (14.07.24)
 */
public class CheckAll {
    @TestFactory
    public Stream<DynamicTest> checkAllKeYFiles() throws IOException {
        var s = Files.walk(Paths.get(".."));
        return s.filter(it -> it.getFileName().toString().endsWith(".key"))
                .map(it -> DynamicTest.dynamicTest(it.getFileName().toString(), () ->
                        Assertions.assertTrue(KeyFormatFacade.checkFile(it))));
    }
}
