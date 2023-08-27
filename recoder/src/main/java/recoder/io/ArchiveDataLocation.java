/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

/**
 * This class implements a data location, that describes an entry of a Java archive file. Currently
 * supported formats are ZIP and JAR.
 *
 * @author RN
 * @author AL
 */
public class ArchiveDataLocation implements DataLocation {

    public static final String LOCATION_TYPE_ARCHIVE = "ARCHIVE";

    /**
     * the archive file
     */
    final ZipFile archiveFile;

    /**
     * the name of the item within the archive
     */
    final String itemName;

    /**
     * creates a new location object.
     *
     * @param archive the file that contains the archive
     * @param itemname the name of the item within the archive
     */
    public ArchiveDataLocation(ZipFile archive, String itemname) {
        archiveFile = archive;
        itemName = itemname;
    }

    /**
     * creates a new location object.
     *
     * @param archivename the name of the archive file
     * @param itemname the name of the item within the archive
     */
    public ArchiveDataLocation(String archivename, String itemname) throws IOException {
        this(new ZipFile(archivename), itemname);
    }

    /**
     * returns the "type" of the data location.
     *
     * @return <tt>LOCATION_TYPE_ARCHIVE</tt>
     */
    public String getType() {
        return LOCATION_TYPE_ARCHIVE;
    }

    /**
     * returns the zip file of this archive.
     *
     * @return the zip file of this archive.
     */
    public ZipFile getFile() {
        return archiveFile;
    }

    /**
     * returns a URL-like string representation of the location in the form " <type>:
     * <location-specific-name>", i.e. file:/bin/sh url:http://mywww/myfile
     * archive:recoder.zip:recoder/java/JavaProgramFactory.class
     */
    public String toString() {
        return getType() + ":" + archiveFile.getName() + "?" + itemName;
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
     * returns an input stream that can be used to read the archive entry content.
     *
     * @return the input stream for reading the data
     * @throws IOException if the stream cannot be created
     */
    public InputStream getInputStream() throws IOException {
        InputStream result = null;
        ZipEntry ze = archiveFile.getEntry(itemName);
        result = new BufferedInputStream(archiveFile.getInputStream(ze));
        return result;
    }

    /**
     * tells the location, that the earlier created input stream has been closed
     */
    public void inputStreamClosed() {
        // but we don't do anything here
    }

    /**
     * returns a reader for the according data content. The reader is placed on top of an input
     * stream.
     *
     * @return the according reader
     * @throws IOException thrown if an error occurs with retrieving the reader or the underlying
     *         input stream from the according data object.
     */
    public Reader getReader() throws IOException {
        return new InputStreamReader(getInputStream(), StandardCharsets.UTF_8);
    }

    /**
     * tells the location, that the earlier created reader has been closed
     */
    public void readerClosed() {
        inputStreamClosed();
    }

    /**
     * returns false since archives do not provide writa access.
     *
     * @return <tt>false</tt>
     */
    public boolean isWritable() {
        return false;
    }

    /**
     * returns false since archives do not even provide writa access.
     *
     * @return <tt>false</tt>
     */
    public boolean hasWriterSupport() {
        return false;
    }

    /**
     * returns <tt>null</tt>
     *
     * @return <tt>null</tt>
     */
    public OutputStream getOutputStream() {
        return null;
    }

    /**
     * tells the location, that the earlier created output stream has been closed
     */
    public void outputStreamClosed() {
        // nothing to do since this cannot happen
    }

    /**
     * returns <tt>null</tt>
     *
     * @return <tt>null</tt>
     */
    public Writer getWriter() {
        return null;
    }

    /**
     * tells the location, that the earlier created writer has been closed
     */
    public void writerClosed() {
        // nothing to do since this cannot happen
    }

    public boolean equals(Object ob) {
        if (ob instanceof ArchiveDataLocation) {
            return archiveFile.equals(((ArchiveDataLocation) ob).archiveFile);
        }
        return false;
    }

    public int hashCode() {
        return archiveFile.hashCode();
    }

}
