/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.io.*;
import java.nio.charset.StandardCharsets;

/**
 * This class implements a data location that describes aJava source code file.
 *
 * @author RN
 * @author AL
 */
public class DataFileLocation implements DataLocation {

    public static final String LOCATION_TYPE_FILE = "FILE";

    File file;

    String canonicalPath;

    /**
     * Creates a new data file location for the specified file. The file might be changed to its
     * canonical form.
     */
    public DataFileLocation(File f) {
        setFile(f);
    }

    public DataFileLocation(String filename) {
        setFile(new File(filename));
    }

    /**
     * returns a string representation of the locationType
     */
    public String getType() {
        return LOCATION_TYPE_FILE;
    }

    public File getFile() {
        return file;
    }

    private void setFile(File f) {
        file = f;
        try {
            canonicalPath = file.getCanonicalPath();
        } catch (IOException ioe) {
            canonicalPath = file.getAbsolutePath();
        }
    }

    /**
     * returns a URL-like string representation of the location in the form " <type>:
     * <location-specific-name>", i.e. file:/bin/sh url:http://mywww/myfile
     * zip:recoder.zip:recoder/java/JavaProgramFactory.class
     */
    public String toString() {
        return getType() + ":" + file.getPath();
    }

    /**
     * determines whether the data source provides a reader interface. If this is not the case, the
     * reader is placed on top of an input stream, which causes efficiency losses.
     *
     * @return true iff the data location provides reader functionality
     */
    public boolean hasReaderSupport() {
        return true;
    }

    /**
     * returns an input stream for the content of the location
     *
     * @return the according input stream
     * @throws IOException thrown if an error occurs with retrieving the input stream from the
     *         according data object.
     */
    public InputStream getInputStream() throws IOException {
        return new BufferedInputStream(new FileInputStream(file));
    }

    /**
     * tells the location, that the earlier created input stream has been closed
     */
    public void inputStreamClosed() {
        // nothing to do
    }

    /**
     * returns a reader for the according data content. If the data source does not provide a
     * reader, an adapter reader is placed on top of an input stream.
     *
     * @return the according reader
     * @throws IOException thrown if an error occurs with retrieving the reader or the underlying
     *         input stream from the according data object.
     */
    public Reader getReader() throws IOException {
        return new FileReader(file, StandardCharsets.UTF_8);
    }

    /**
     * tells the location, that the earlier created reader has been closed
     */
    public void readerClosed() {
        // nothing to do
    }

    /**
     * determines whether or not the data location can be overwritten.
     *
     * @return true if writing is supported
     */
    public boolean isWritable() {
        return true;
    }

    /**
     * determines whether the data source provides a writer interface. If this is not the case, the
     * writer is placed on top of an output stream, which causes efficiency losses.
     *
     * @return true iff the data location provides writer functionality
     */
    public boolean hasWriterSupport() {
        return true;
    }

    /**
     * returns an output stream for manipulating the content of the location
     *
     * @return the according output stream
     * @throws IOException thrown if an error occurs with retrieving the output stream from the
     *         according data object.
     */
    public OutputStream getOutputStream() throws IOException {
        return new FileOutputStream(file);
    }

    /**
     * tells the location, that the earlier created output stream has been closed
     */
    public void outputStreamClosed() {
        // nothing to do
    }

    /**
     * returns a writer for the according data content. If the data source does not provide a
     * writer, an adapter reader is placed on top of an output stream.
     *
     * @return the according writer
     * @throws IOException thrown if an error occurs with retrieving the writer or the underlying
     *         output stream from the according data object.
     */
    public Writer getWriter() throws IOException {
        return new FileWriter(file, StandardCharsets.UTF_8);
    }

    /**
     * tells the location, that the earlier created writer has been closed
     */
    public void writerClosed() {
        // nothing to do
    }

    public boolean equals(Object ob) {
        if (ob instanceof DataFileLocation) {
            return canonicalPath.equals(((DataFileLocation) ob).canonicalPath);
        }
        return false;
    }

    public int hashCode() {
        return canonicalPath.hashCode();
    }

}
