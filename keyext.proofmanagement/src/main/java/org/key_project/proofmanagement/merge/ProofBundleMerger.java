package org.key_project.proofmanagement.merge;

import org.key_project.proofmanagement.check.ProofManagementException;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.Logger;
import org.key_project.proofmanagement.io.ProofBundleHandler;

import java.io.IOException;
import java.net.URI;
import java.nio.file.*;
import java.util.HashMap;
import java.util.List;

public class ProofBundleMerger {
    private ProofBundleMerger() {
    }

    /**
     * This method merges n proof bundles into a single one.
     * @param inputs the paths to the input bundles to merge
     * @param output the target path (will be zipped)
     * @throws ProofManagementException if any of the files can not be accessed
     */
    public static void merge(List<Path> inputs, Path output, boolean force, Logger logger)
        throws ProofManagementException {

        boolean consistent = FilesChecker.listOfPathsConsistent(inputs);
        if (consistent) {
            logger.print(LogLevel.INFO, "All files in the bundles are consistent. Continuing the"
                + " merge ...");
        } else {
            logger.print(LogLevel.WARNING, "The files in the bundles are inconsistent. If you want "
                + "to merge nonetheless, use the \"--force\" option.");
        }

        if (consistent || force) {
            try {
                // TODO: at the moment, if the target file already exists, we silently overwrite it
                if (Files.exists(output)) {
                    Files.delete(output);
                }

                final Path absZipOutput = output.toAbsolutePath().normalize();

                // The filesystem only works when the extension is zip -> remove later!
                URI uri = URI.create("jar:" + absZipOutput.toUri() + ".zip");

                // create zip file system to write to
                HashMap<String, String> env = new HashMap<>();
                env.put("create", "true");
                try (FileSystem fs = FileSystems.newFileSystem(uri, env)) {
                    for (Path p : inputs) {
                        try (ProofBundleHandler pbh = ProofBundleHandler.createBundleHandler(p)) {
                            List<Path> allJavaFiles = pbh.getSourceFiles();
                            allJavaFiles.addAll(pbh.getClasspathFiles());
                            Path bcp = pbh.getBootclasspath();
                            if (bcp != null && Files.exists(bcp)) {
                                try (var paths = Files.walk(bcp)) {
                                    paths.filter(f -> f.endsWith(".java")).forEach(
                                        allJavaFiles::add);
                                }
                            }

                            // merge Java sources from all bundles
                            for (Path sourceFile : allJavaFiles) {
                                Path absJavaFile = sourceFile.toAbsolutePath().normalize();
                                Path rel = pbh.relativize(absJavaFile);
                                Path internal = fs.getPath(rel.toString());

                                // skip existing (we know due to our previous check that its equal)
                                if (!Files.exists(internal)) {
                                    Files.createDirectories(internal.getParent());
                                    Files.copy(sourceFile, internal,
                                        StandardCopyOption.REPLACE_EXISTING);
                                }
                            }

                            // add .proof files
                            for (Path proofFile : pbh.getProofFiles()) {
                                Path absProofFile = proofFile.toAbsolutePath().normalize();
                                Path rel = pbh.relativize(absProofFile);
                                Path internal = fs.getPath(rel.toString());
                                Files.copy(proofFile, internal,
                                    StandardCopyOption.REPLACE_EXISTING);
                            }

                            // add .key files
                            for (Path keyFile : pbh.getKeYFiles()) {
                                Path absKeyFile = keyFile.toAbsolutePath().normalize();
                                Path rel = pbh.relativize(absKeyFile);
                                Path internal = fs.getPath(rel.toString());
                                Files.copy(keyFile, internal, StandardCopyOption.REPLACE_EXISTING);
                            }
                        }
                    }
                }
                // remove artificial .zip extension from target file
                Files.move(Paths.get(absZipOutput + ".zip"), output);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
}
