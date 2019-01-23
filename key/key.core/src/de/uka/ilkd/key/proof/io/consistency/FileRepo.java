package de.uka.ilkd.key.proof.io.consistency;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;

/**
 * This interface provides access to files.
 * In addition, it can be used to save a consistent zip bundle containing all proof relevant files.
 *
 * @author Wolfram Pfeifer
 */
public interface FileRepo extends ProofDisposedListener {
    /**
     * Provides access to a file on disk.
     * @param path the path of the file
     * @return an InputStream of the requested file
     * @throws FileNotFoundException if the file does not exist
     * @throws IOException on IO errors, e.g. if the user has no permission to read the file
     */
    public InputStream getInputStream(Path path) throws FileNotFoundException, IOException;

    /**
     * This method can be used to write a file that has no counterpart outside to the FileRepo.
     * @param path the path of the file to store. The path must be relative to the base directory
     *      of the proof package.
     * @return an OutputStream to the file in the FileRepo
     * @throws FileNotFoundException if a file with the given path exists
     */
    public OutputStream createOutputStream(Path path) throws FileNotFoundException;

    /**
     * Register the proof in the FileRepo.
     * @param proof the proof to register
     */
    public void registerProof(Proof proof);

    /**
     * Stores all files stored in the FileRepo in a consistent package as a ZIP archive at the given
     * target path. If a file with the given path exists, it is deleted first.
     * @param savePath the target path of the ZIP archive
     * @throws IOException on IO errors, e.g. if the user has no permission to write at the path
     */
    public void saveProof(Path savePath) throws IOException;

    /**
     * Sets the bootclasspath (containing available classes from the Java Class Library).
     * @param path the bootclasspath to set
     */
    public void setBootClassPath(File path);

    /**
     * Sets the classpath.
     * @param classPath the classpath to set
     */
    public void setClassPath(List<File> classPath);

    /**
     * Sets the java path (where the source files are located).
     * @param javaPath the java path to set
     */
    public void setJavaPath(String javaPath);

    /**
     * Sets the base directory of the proof, i.e. the main directory where the proof is loaded from.
     * When loading Java sources this is the directory the loaded file resides in.
     * When loading .key-Files this is the directory specified via "\\javaSource" or the directory
     * of the .key-File, if no source directory is specified.
     *
     * This is needed by the FileRepo for resolving pathnames.
     *
     * @param path The path of the base directory. If a file is given, then its parent directory is
     *             set as base path
     */
    public void setBaseDir(Path path);
}
