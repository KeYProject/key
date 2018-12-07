package consistencyChecking;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.HashMap;
import java.util.HashSet;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.IOUtil;

import io.PackageHandler;

public class FileConsistencyChecker {
    
    public Path merge(ImmutableList<Path> paths, Path newZProofDir) {
        if (new SettingsChecker().check(paths) && listOfPathsConsistent(paths)) {

            // only add source files from first package
            PackageHandler referencePh = new PackageHandler(paths.head());

            try {
                for (Path sourceFile : referencePh.getClasspathFiles()) {
                    Path relativePath = paths.head().relativize(sourceFile);
                    Path newAbsolutePath = newZProofDir.resolve(relativePath);
                    Files.copy(sourceFile, newAbsolutePath);
                }

                // add proof and key files from all packages
                for (Path p : paths) {
                    PackageHandler ph = new PackageHandler(p);

                    for (Path proofFilePath : ph.getProofFiles()) {
                        Path relativePath = p.relativize(proofFilePath);
                        Path newAbsolutePath = newZProofDir.resolve(relativePath);
                        Files.copy(proofFilePath, newAbsolutePath);
                    }
                    for (Path keyFilePath : ph.getKeYFiles()) {
                        Path relativePath = p.relativize(keyFilePath);
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
    
    private boolean listOfPathsConsistent(ImmutableList<Path> paths) {
        boolean res = true;
        Path reference = paths.head();
        for (Path p : paths.tail()) {
            res &= classpathsConsistent(p,  reference);
        }
        return res;
    }
    
    private boolean classpathsConsistent(Path pathA, Path pathB) {
        PackageHandler pa = new PackageHandler(pathA);
        PackageHandler pb = new PackageHandler(pathB);
        ImmutableList<Path> classpathFilesA = null;
        ImmutableList<Path> classpathFilesB = null;
        try {
            classpathFilesA = pa.getClasspathFiles();
            classpathFilesB = pb.getClasspathFiles();
            if (classpathFilesA.size() != classpathFilesB.size()) {
                return false;
            }
        } catch (IOException e1) {
            e1.printStackTrace();
        }
        
        HashMap<Path, byte[]> mapA= new HashMap<Path, byte[]>();
        HashMap<Path, byte[]> mapB= new HashMap<Path, byte[]>();
        try {
            for (Path p : classpathFilesA) {
                mapA.put(p, createChecksum(p.getFileName().toString()));
            }
            for (Path p : classpathFilesB) {
                mapB.put(p, createChecksum(p.getFileName().toString()));
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
        
        for (Path p : mapA.keySet()) {
            if (!mapB.containsKey(p) || !(mapA.get(p) == mapB.get(p))) {
                return false;
            }
        }
        return true;
    }
    
    public static byte[] createChecksum(String filename) throws Exception {
        InputStream fis =  new FileInputStream(filename);

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

}
