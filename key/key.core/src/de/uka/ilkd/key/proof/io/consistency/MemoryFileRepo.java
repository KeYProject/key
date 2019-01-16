package de.uka.ilkd.key.proof.io.consistency;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Path;

/**
 * This class uses the memory as a store for the proof-relevant files.
 *
 * @author Wolfram Pfeifer
 */
public class MemoryFileRepo extends AbstractFileRepo {

    @Override
    public InputStream getFile(Path path) throws FileNotFoundException, IOException {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public OutputStream createOutputStream(Path path) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public InputStream getInputStream(Path p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Path getSaveName(Path path) {
        // TODO Auto-generated method stub
        return null;
    }
}
