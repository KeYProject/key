package de.uka.ilkd.key.experimental;

import java.io.File;
import org.antlr.runtime.Token;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class FileWithTestProperty {

    private final TestProperty testProperty;
    private final Token pathToken;
    private final File keyFile;

    public FileWithTestProperty(TestProperty testProperty, Token pathToken) {
        this.pathToken = pathToken;
        this.testProperty = testProperty;
        String initialDirecotry = System.getenv("KEY_HOME") + "/key/key.ui/examples/";
        String absolutePath = initialDirecotry + pathToken.getText();
        keyFile = new File(absolutePath);
    }

    public File getFile() throws ParserSemanticException {
        if (keyFile.isDirectory()) {
            String exceptionMessage = "Expecting a file, but found a directory: " + keyFile.getAbsolutePath();
            throw new ParserSemanticException(pathToken, exceptionMessage);
        }
        if (!keyFile.exists()) {
            String exceptionMessage = "The given file does not exist: " + keyFile.getAbsolutePath();
            throw new ParserSemanticException(pathToken, exceptionMessage);
        }
        return keyFile;
    }

}
