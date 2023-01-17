package de.uka.ilkd.key.core;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URL;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import org.key_project.util.java.IOUtil;


public class WebstartMain {

    private static final int BUFFER_SIZE = 4096;


    public static File setupExamples() {
        try {
            URL examplesURL = WebstartMain.class.getResource("/examples.zip");
            if (examplesURL == null) {
                throw new IOException("Missing examples.zip in resources");
            }

            File tempDir = createTempDirectory();

            try (ZipInputStream zis = new ZipInputStream(examplesURL.openStream())) {
                byte[] buffer = new byte[BUFFER_SIZE];

                for (ZipEntry zipEntry = zis.getNextEntry(); zipEntry != null; zipEntry =
                    zis.getNextEntry()) {


                    String entryName = zipEntry.getName();
                    File outFile = new File(tempDir, entryName);

                    if (zipEntry.isDirectory()) {

                        boolean mkdirSuccess = outFile.mkdir();
                        if (!mkdirSuccess) {
                            throw new IOException("Cannot create directory " + outFile);
                        }

                    } else {

                        try (FileOutputStream fos = new FileOutputStream(outFile)) {
                            int n;
                            while ((n = zis.read(buffer, 0, BUFFER_SIZE)) > -1) {
                                fos.write(buffer, 0, n);
                            }
                        }
                        zis.closeEntry();
                    }
                }
            }
            return tempDir;
        } catch (IOException e) {
            e.printStackTrace();
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
