package de.uka.ilkd.key.proof.io.consistency;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.RuleSource;

/**
 * This interface provides access to files.
 * In addition, it can be used to save a consistent zip bundle containing all proof relevant files.
 *
 * @author Wolfram Pfeifer
 */
public interface FileRepo {
    /**
     * Provides access to a file on disk.
     * @param path the path of the file
     * @return an InputStream of the requested file
     * @throws FileNotFoundException if the file does not exist
     * @throws IOException on IO errors, e.g. if the user has no permission to read the file
     */
    public InputStream getFile(Path path) throws FileNotFoundException, IOException;

    /**
     * Sets the boot class path (containing available classes from the Java Class Library).
     * @param path the boot class path to set
     */
    public void setBootClassPath(Path path);

    /**
     * Sets the class path.
     * @param path the class path to set
     */
    public void setClassPath(Path path);

    /**
     * Sets the java path (where the source files are located).
     * @param path the java path to set
     */
    public void setJavaPath(Path path);

    /**
     * Stores the given proof and all files relevant for the proof in a consistent bundle as a ZIP
     * archive at the given target path.
     * @param path the target path of the ZIP archive
     * @param proof the given proof to save
     * @throws IOException on IO errors, e.g. if the user has no permission to write at the path
     */
    public void saveProof(Path path, Proof proof) throws IOException;
    
    //public RuleSource getRuleSource(Path p);

    public void setBaseDir(Path path);

    //public File getOriginalFile(File file);
}
