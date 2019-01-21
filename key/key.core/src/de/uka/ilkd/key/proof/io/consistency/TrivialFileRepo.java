package de.uka.ilkd.key.proof.io.consistency;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Path;

/**
 * This FileRepo does not cache any files but writes to / reads from the original files on disk.
 * It can be used for recreating the old behavior of KeY without a FileRepo.
 * @author Wolfram Pfeifer
 */
public class TrivialFileRepo extends AbstractFileRepo {

    @Override
    public InputStream getInputStream(Path path) throws FileNotFoundException, IOException {
        files.add(path);
        return new FileInputStream(path.toFile());
    }

    @Override
    public OutputStream createOutputStream(Path path) throws FileNotFoundException {
        // TODO: create correct zip structure here, or other solution for saving zip
        files.add(path);

        return new FileOutputStream(path.toFile());
    }

    @Override
    public InputStream getInputStreamInternal(Path p) throws FileNotFoundException {
        return new FileInputStream(p.toFile());
    }

    @Override
    public Path getSaveName(Path path) {
        return baseDir.relativize(path);
    }
}
