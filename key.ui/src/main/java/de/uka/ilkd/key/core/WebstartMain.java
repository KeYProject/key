package de.uka.ilkd.key.core;

import java.io.File;
import java.io.IOException;
import java.net.URL;

import org.key_project.util.java.IOUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public class WebstartMain {
    private static final Logger LOGGER = LoggerFactory.getLogger(WebstartMain.class);

    private static final int BUFFER_SIZE = 4096;


    public static File setupExamples() {
        try {
            URL examplesURL = WebstartMain.class.getResource("/examples.zip");
            if (examplesURL == null) {
                throw new IOException("Missing examples.zip in resources");
            }

            File tempDir = createTempDirectory();

            if (tempDir != null) {
                IOUtil.extractZip(examplesURL.openStream(), tempDir.toPath());
            }
            return tempDir;
        } catch (IOException e) {
            LOGGER.warn("Error setting up examples", e);
            return null;
        }
    }


    private static File createTempDirectory() throws IOException {
        final File tempDir = File.createTempFile("keyheap-examples-", null);
        tempDir.delete();
        if (!tempDir.mkdir()) {
            return null;
        }
        Runtime.getRuntime().addShutdownHook(new Thread(() -> IOUtil.delete(tempDir)));
        return tempDir;
    }


    public static void main(String[] args) {
        File examplesDir = setupExamples();

        if (examplesDir != null) {
            String[] newArgs = new String[args.length + 2];
            System.arraycopy(args, 0, newArgs, 0, args.length);
            newArgs[args.length] = "--examples";
            newArgs[args.length + 1] = examplesDir.getAbsolutePath();
            args = newArgs;
        }

        Main.main(args);
    }
}
