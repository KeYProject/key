package proofmanagement.consistencyChecking;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

import proofmanagement.io.PackageHandler;

/**
 * This class tests if all given proof is consistent w.r.t. the files contained.
 */
public class FileConsistencyChecker implements Checker {
    
    public static Path merge(List<Path> paths, Path newZProofDir) {
        // TODO: individual checkers should not depend on each other
        if (new SettingsChecker().check(paths).isConsistent() && listOfPathsConsistent(paths)) {

            // only add source files from first package
            PackageHandler referencePh = new PackageHandler(paths.get(0));

            try {
                for (Path sourceFile : referencePh.getClasspathFiles()) {
                    Path relativePath = referencePh.getDir().relativize(sourceFile);
                    Path newAbsolutePath = newZProofDir.resolve(relativePath);
                    Files.copy(sourceFile, newAbsolutePath);
                }

                // add proof and key files from all packages
                for (Path p : paths) {
                    PackageHandler ph = new PackageHandler(p);

                    for (Path proofFilePath : ph.getProofFiles()) {
                        Path relativePath = ph.getDir().relativize(proofFilePath);
                        Path newAbsolutePath = newZProofDir.resolve(relativePath);
                        Files.copy(proofFilePath, newAbsolutePath);
                    }
                    for (Path keyFilePath : ph.getKeYFiles()) {
                        Path relativePath = ph.getDir().relativize(keyFilePath);
                        Path newAbsolutePath = newZProofDir.resolve(relativePath);
                        Files.copy(keyFilePath, newAbsolutePath);
                    }
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        return newZProofDir;
    }
    
    private static boolean listOfPathsConsistent(List<Path> paths) {
        boolean res = true;
        Path reference = paths.get(0);
        for (int i = 1; i < paths.size(); i++) {
            Path p = paths.get(i);
            res &= classpathsConsistent(p,  reference);
        }
        return res;
    }
    
    private static boolean classpathsConsistent(Path pathA, Path pathB) {
        PackageHandler pa = new PackageHandler(pathA);
        PackageHandler pb = new PackageHandler(pathB);
        List<Path> classpathFilesA = null;
        List<Path> classpathFilesB = null;
        try {
            classpathFilesA = pa.getClasspathFiles();
            classpathFilesB = pb.getClasspathFiles();
            if (classpathFilesA.size() != classpathFilesB.size()) {
                return false;
            }
        } catch (IOException e1) {
            e1.printStackTrace();
        }
        
        HashMap<Path, byte[]> mapA = new HashMap<>();
        HashMap<Path, byte[]> mapB = new HashMap<>();
        try {
            for (Path p : classpathFilesA) {
                mapA.put(p, createMd5Checksum(p));
            }
            for (Path p : classpathFilesB) {
                mapB.put(p, createMd5Checksum(p));
            }
        } catch (Exception e) {
            e.printStackTrace();
        }

        // check if all files
        for (Path p : mapA.keySet()) {
            if (!mapB.containsKey(p) || !(Arrays.equals(mapA.get(p), mapB.get(p)))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Reads the file with the given path and computes the md5 checksum of it.
     * @param path path of the file
     * @return md5 checksum of the file
     * @throws NoSuchAlgorithmException if the MD5 checksum is not available for some reason
     * @throws IOException if the file with the given path does not exist or can not be read
     */
    public static byte[] createMd5Checksum(Path path) throws NoSuchAlgorithmException, IOException {
        InputStream fis = new FileInputStream(path.toFile());

        byte[] buffer = new byte[1024];
        MessageDigest complete = MessageDigest.getInstance("MD5");
        int numRead;

        do {
            numRead = fis.read(buffer);
            if (numRead > 0) {
                complete.update(buffer, 0, numRead);
            }
        } while (numRead != -1);

        fis.close();
        return complete.digest();
    }

    @Override
    public CheckResult check(List<Path> proofFiles) {
        return new CheckResult(listOfPathsConsistent(proofFiles));
    }
}
