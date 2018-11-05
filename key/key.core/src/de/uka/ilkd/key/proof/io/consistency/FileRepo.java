package de.uka.ilkd.key.proof.io.consistency;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Path;

import de.uka.ilkd.key.proof.Proof;

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
    public InputStream getFile(Path path) throws FileNotFoundException, IOException; // TODO: naming

    /**
     * This method can be used to write a file to the FileRepo.
     * @param path the path of the file to store (relative to the base directory of the proof)
     * @return an OutputStream to the file in the FileRepo
     */
    public OutputStream createOutputStream(Path path);

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
     * @param savePath the target path of the ZIP archive
     * @param proof the given proof to save
     * @throws IOException on IO errors, e.g. if the user has no permission to write at the path
     */
    public void saveProof(Path savePath, Proof proof) throws IOException;

    /**
     * Sets the base directory of the proof, i.e. the main directory where the proof is loaded from.
     * When loading Java sources this is the directory the loaded file resides in.
     * When loading .key-Files this is the directory specified via "\\javaSource" or the directory
     * of the .key-File, if no source directory is specified.
     *
     * This is needed by the FileRepo for resolving pathnames.
     *
     * @param path the path of the base directory
     */
    public void setBaseDir(Path path);

    /**
     * Gets the base directory.
     * See JavaDoc of {@link #setBaseDir(Path)} for further explanation.
     * @return the path of the base directory
     */
    public Path getBaseDir();

    /**
     * Clears all data in the FileRepo and marks it as disposed.
     */
    public void dispose();
}
