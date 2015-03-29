package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;

import org.antlr.runtime.Token;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class FileWithTestProperty implements Serializable {

    final TestProperty testProperty;
    final String path;
    final File keyFile;

    public FileWithTestProperty(TestProperty testProperty, Token pathToken) {
        this.path = pathToken.getText();
        this.testProperty = testProperty;
        String initialDirecotry = System.getenv("KEY_HOME") + "/key/key.ui/examples/";
        String absolutePath = initialDirecotry + pathToken.getText();
        keyFile = new File(absolutePath);
    }

    public File getFile() throws IOException {
        if (keyFile.isDirectory()) {
            String exceptionMessage = "Expecting a file, but found a directory: " + keyFile.getAbsolutePath();
            throw new IOException(exceptionMessage);
        }
        if (!keyFile.exists()) {
            String exceptionMessage = "The given file does not exist: " + keyFile.getAbsolutePath();
            throw new IOException(exceptionMessage);
        }
        return keyFile;
    }

}
