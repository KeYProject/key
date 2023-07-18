package org.key_project.proofmanagement.merge;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

import org.key_project.proofmanagement.io.ProofBundleHandler;

import javax.annotation.Nonnull;

// IMPORTANT: difference from other checkers: works with multiple packages instead of a single
//          bundle!
/**
 * This class tests if all given proof is consistent w.r.t. the files contained.
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
            // TODO: be careful, compare with implicit bcp files!
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
        return false;
        //return pathsConsistent(a, b, ProofBundleHandler::getBootclasspath);
    }

    // two paths are considered consistent if all files (recursively) inside pathA have a
    // counterpart in b (with same location and same content!)
    // However, both paths may contain additional unique files.
    private static boolean pathsConsistent(Path a, Path b, CheckedFunction<ProofBundleHandler, List<Path>> f) {
        List<Path> filesA = new ArrayList<>();
        List<Path> filesB = new ArrayList<>();
        try (ProofBundleHandler pha = ProofBundleHandler.createBundleHandler(a);
             ProofBundleHandler phb = ProofBundleHandler.createBundleHandler(b)) {
            filesA = f.apply(pha);
            filesB = f.apply(phb);

            // does not have to be same size (a bundle may add files)
            //if (filesA.size() != filesB.size()) {
            //    return false;
            //}

            HashMap<Path, byte[]> mapA = new HashMap<>();
            HashMap<Path, byte[]> mapB = new HashMap<>();
            try {
                for (Path p : filesA) {
                    mapA.put(p, createSHA256Checksum(p));
                }
                for (Path p : filesB) {
                    mapB.put(p, createSHA256Checksum(p));
                }
            } catch (Exception e) {
                e.printStackTrace();
            }

            // check if all files contained in both classpaths are equal
            for (Path p : mapA.keySet()) {
                if (mapB.containsKey(p) && !(Arrays.equals(mapA.get(p), mapB.get(p)))) {
                    return false;
                }
            }
        } catch (IOException e1) {
            e1.printStackTrace();
        } catch (Exception e) {
            e.printStackTrace();
        }

        return true;
    }

    /**
     * Reads the file with the given path and computes the SHA256 checksum of it.
     * @param path path of the file
     * @return md5 checksum of the file
     * @throws NoSuchAlgorithmException if the MD5 checksum is not available for some reason
     * @throws IOException if the file with the given path does not exist or can not be read
     */
    public static byte[] createSHA256Checksum(Path path) throws NoSuchAlgorithmException, IOException {
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
    @Override
    public CheckResult check(List<Path> proofFiles) {
        return new CheckResult(listOfPathsConsistent(proofFiles));
    }*/
}
