package de.uka.ilkd.key.util;

import java.io.IOException;
import java.io.InputStream;

import recoder.io.DataLocation;

/**
 * This class encapsulates a collection of files which is arbitrarily organised.
 * It is iterable and returns all files (not directories) during the iteration
 * as streams.
 * 
 * Subclasses allow to iterate a jar/zip-file or a directory.
 * 
 * @author MU
 */

public interface FileCollection {

    public Walker createWalker(String extension) throws IOException;

    public interface Walker {

        public boolean step();

        public String getCurrentName();
        
        public DataLocation getCurrentDataLocation();
        
        public String getType();

        public InputStream openCurrent() throws IOException;
    }
}
