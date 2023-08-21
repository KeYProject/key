/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.merge;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.*;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;

import org.key_project.proofmanagement.io.ProofBundleHandler;

/**
 * This class tests if all given proof is consistent w.r.t. the files contained.
 *
 * @author Wolfram Pfeifer
 */
public class FilesChecker {
    @FunctionalInterface
    public interface CheckedFunction<T, R> {
        R apply(T t) throws IOException;
    }

    static boolean listOfPathsConsistent(@Nonnull List<Path> paths) {
        boolean res = true;
        Path reference = paths.get(0);
        for (int i = 1; i < paths.size(); i++) {
            Path p = paths.get(i);
            res &= sourcesConsistent(p, reference);
            res &= classpathsConsistent(p, reference);
            res &= bootclasspathsConsistent(p, reference);
        }
        return res;
    }

    private static boolean sourcesConsistent(Path a, Path b) {
        return pathsConsistent(a, b, ProofBundleHandler::getSourceFiles);
    }

    private static boolean classpathsConsistent(Path a, Path b) {
        return pathsConsistent(a, b, ProofBundleHandler::getClasspathFiles);
    }

    private static boolean bootclasspathsConsistent(Path a, Path b) {
        /*
         * TODO: At the moment, we do not compare internal/implicit bcp (JavaRedux shipped with KeY)
         * and explicitly given bcp, i.e. we might consider the bcps mistakenly inconsistent.
         * We might relax that for the future.
         */
        return pathsConsistent(a, b, FilesChecker::collectBcpFiles);
    }

    private static List<Path> collectBcpFiles(ProofBundleHandler pbh) throws IOException {
        Path bcp = pbh.getBootclasspath();
        if (bcp == null) {
            return Collections.emptyList();
        }
        try (var files = Files.walk(pbh.getBootclasspath())) {
            return files.collect(Collectors.toUnmodifiableList());
        }
    }

    /*
     * Two paths are considered consistent if all files (recursively) inside pathA which are also
     * present in b (at the same location) have the same content. However, both paths are allowed to
     * contain additional unique files.
     */
    private static boolean pathsConsistent(Path a, Path b,
            CheckedFunction<ProofBundleHandler, List<Path>> f) {
        try (ProofBundleHandler pha = ProofBundleHandler.createBundleHandler(a);
                ProofBundleHandler phb = ProofBundleHandler.createBundleHandler(b)) {
            List<Path> filesA = f.apply(pha);
            List<Path> filesB = f.apply(phb);

            HashMap<Path, byte[]> mapA = new HashMap<>();
            HashMap<Path, byte[]> mapB = new HashMap<>();
            try {
                for (Path p : filesA) {
                    Path abs = p.toAbsolutePath().normalize();
                    mapA.put(pha.relativize(abs), createSHA256Checksum(p));
                }
                for (Path p : filesB) {
                    Path abs = p.toAbsolutePath().normalize();
                    mapB.put(phb.relativize(abs), createSHA256Checksum(p));
                }
            } catch (Exception e) {
                e.printStackTrace();
            }

            // check if all files contained in both paths are equal
            for (Path p : mapA.keySet()) {
                if (mapB.containsKey(p) && !(Arrays.equals(mapA.get(p), mapB.get(p)))) {
                    return false;
                }
            }
        } catch (IOException e1) {
            e1.printStackTrace();
        }

        return true;
    }

    /**
     * Reads the file with the given path and computes the SHA256 checksum of it.
     *
     * @param path path of the file
     * @return md5 checksum of the file
     * @throws NoSuchAlgorithmException if the MD5 checksum is not available for some reason
     * @throws IOException if the file with the given path does not exist or can not be read
     */
    public static byte[] createSHA256Checksum(Path path)
            throws NoSuchAlgorithmException, IOException {
        MessageDigest complete = MessageDigest.getInstance("SHA-256");
        try (InputStream fis = new FileInputStream(path.toFile())) {
            byte[] buffer = new byte[1024];
            int numRead;

            do {
                numRead = fis.read(buffer);
                if (numRead > 0) {
                    complete.update(buffer, 0, numRead);
                }
            } while (numRead != -1);
        }
        return complete.digest();
    }

    /*
     * @Override
     * public CheckResult check(List<Path> proofFiles) {
     * return new CheckResult(listOfPathsConsistent(proofFiles));
     * }
     */
}
