package consistencyChecking;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.HashMap;
import java.util.HashSet;

import org.key_project.util.collection.ImmutableList;
import io.PackageHandler;

public class FileConsistencyChecker {
    
    private boolean listOfPathsConsistent(ImmutableList<Path> paths) {
        boolean res = true;
        Path reference = paths.head();
        for (Path p : paths.tail()) {
            res &= packagesConsistent(p,  reference);
        }
        return res;
    }
    
    private boolean packagesConsistent(Path pathA, Path pathB) {
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
        
//        for (Path p : )
        return false;
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
