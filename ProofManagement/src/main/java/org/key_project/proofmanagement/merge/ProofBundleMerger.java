package org.key_project.proofmanagement.merge;

import org.key_project.proofmanagement.io.ProofBundleHandler;

import java.io.IOException;
import java.net.URI;
import java.nio.file.*;
import java.util.HashMap;
import java.util.List;

public class ProofBundleMerger {
    // TODO: output is assumed to be absolute
    public static void merge(List<Path> inputs, Path output) {
        if (FilesChecker.listOfPathsConsistent(inputs)) {
            try {
                final Path absZipOutput = output.toAbsolutePath();
                HashMap<String, String> env = new HashMap<>();
                env.put("create", "true");

                // create zip file system to write to
                URI abs = absZipOutput.normalize().toUri();
                FileSystem fs = FileSystems.newFileSystem(URI.create("jar:" + abs), env);

                for (Path p : inputs) {
                    ProofBundleHandler ph = new ProofBundleHandler(p);
                    try {
                        List<Path> allJavaFiles = ph.getSourceFiles();
                        allJavaFiles.addAll(ph.getClasspathFiles());
                        allJavaFiles.addAll(ph.getBootclasspathFiles());

                        // merge sources from all packages
                        // TODO: possible problem with bootclasspath (implicit vs. explicit)
                        for (Path sourceFile : allJavaFiles) {
                            Path rel = ph.getDir().relativize(sourceFile);
                            Path internal = fs.getPath(rel.toString());

                            // skip existing (we know due to our previous check that its equal)
                            if (!Files.exists(internal)) {
                                Files.createDirectories(internal.getParent());
                                Files.copy(sourceFile, internal, StandardCopyOption.REPLACE_EXISTING);
                            }
                        }

                        // add .proof files
                        for (Path proofFilePath : ph.getProofFiles()) {
                            Path relativePath = ph.getDir().relativize(proofFilePath);
                            Path newAbsolutePath = fs.getPath(relativePath.toString());
                            // TODO: check that replace_existing is correct option
                            Files.copy(proofFilePath, newAbsolutePath, StandardCopyOption.REPLACE_EXISTING);
                        }

                        // add .key files
                        for (Path keyFilePath : ph.getKeYFiles()) {
                            Path relativePath = ph.getDir().relativize(keyFilePath);
                            Path newAbsolutePath = fs.getPath(relativePath.toString());
                            Files.copy(keyFilePath, newAbsolutePath);
                        }
                    } finally {
                        ph.dispose();
                    }
                }
                fs.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
}
