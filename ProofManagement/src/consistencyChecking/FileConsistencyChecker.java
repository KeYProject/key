package consistencyChecking;

import java.io.FileInputStream;
import java.io.InputStream;
import java.nio.file.Path;
import java.security.MessageDigest;
import org.key_project.util.collection.ImmutableList;

public class FileConsistencyChecker {
    
    private boolean filesConsistent(ImmutableList<Path> paths) {
        for (Path p : paths) {
            PackageHandler ph;
        }
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
