package de.uka.ilkd.key.proof.io.consistency;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.nio.file.Path;

import de.uka.ilkd.key.proof.io.RuleSource;

/**
 * This FileRepo does not cache any files but writes to / reads from the original files on disk.
 * It can be used for recreating the old behavior of KeY without a FileRepo.
 * @author Wolfram Pfeifer
 */
public class TrivialFileRepo extends AbstractFileRepo {
    @Override
    public InputStream getInputStream(Path path) throws FileNotFoundException, IOException {

        // wrap path into URL for uniform treatment
        return getInputStream(path.toUri().toURL());
//
//        // ignore URL files (those are internal files shipped with KeY)
//        if (isURLFile(path)) {
//            return getInputStream(path.toUri().toURL());
//        }
//
//        // TODO: handle gz files here
//        // TODO: same problem should be in DiskFileRepo
//        if (path.toString().endsWith(".proof.gz")) {
//            // ignore *.proof.gz files to force old behavior
//            return null;
//        }
//
//        //addFile(path);
//        return new FileInputStream(path.toFile());
    }

    @Override
    public InputStream getInputStream(RuleSource ruleSource) {
        return ruleSource.getNewStream();
    }

    @Override
    public InputStream getInputStream(URL url) throws IOException {
        return url.openStream();
    }

    @Override
    public OutputStream createOutputStream(Path path) throws FileNotFoundException {
        // TODO: create correct zip structure here, or other solution for saving zip
        //addFile(path);
        return new FileOutputStream(path.toFile());
    }

    @Override
    public InputStream getInputStreamInternal(Path p) throws FileNotFoundException {
        return new FileInputStream(p.toFile());
    }

    @Override
    public Path getSaveName(Path path) {
        return getBaseDir().relativize(path);
    }
}
