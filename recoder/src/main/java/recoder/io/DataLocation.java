/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.io.*;

/**
 * Describes the origin of source or object data, such as files, URLs, or archive entries. Locations
 * can open an input stream and provide detailed information about further streams that are
 * supported by the location. It supports output streams, readers and writers in case these are
 * feasible.
 *
 * @author RN
 * @author AL
 */
public interface DataLocation {

    /**
     * returns a string representation of the locationType
     */
    String getType();

    /**
     * returns a URL-like string representation of the location in the form " <type>:
     * <location-specific-name>", i.e. file:/bin/sh url:http://mywww/myfile
     * zip:recoder.zip:recoder/java/JavaProgramFactory.class
     */
    String toString();

    /**
     * determines whether the data source provides a reader interface. If this is not the case, the
     * reader is placed on top of an input stream, which causes efficiency losses.
     *
     * @return true iff the data location provides reader functionality
     */
    boolean hasReaderSupport();

    /**
     * returns an input stream for the content of the location
     *
     * @return the according input stream
     * @throws IOException thrown if an error occurs with retrieving the input stream from the
     *         according data object.
     */
    InputStream getInputStream() throws IOException;

    /**
     * tells the location, that the earlier created input stream has been closed
     */
    void inputStreamClosed();

    /**
     * returns a reader for the according data content. If the data source does not provide a
     * reader, an adapter reader is placed on top of an input stream.
     *
     * @return the according reader
     * @throws IOException thrown if an error occurs with retrieving the reader or the underlying
     *         input stream from the according data object.
     */
    Reader getReader() throws IOException;

    /**
     * tells the location, that the earlier created reader has been closed
     */
    void readerClosed();

    /**
     * determines whether or not the data location can be overwritten.
     *
     * @return true if writing is supported
     */
    boolean isWritable();

    /**
     * determines whether the data source provides a writer interface. If this is not the case, the
     * writer is placed on top of an output stream, which causes efficiency losses.
     *
     * @return true iff the data location provides writer functionality
     */
    boolean hasWriterSupport();

    /**
     * returns an output stream for manipulating the content of the location
     *
     * @return the according output stream
     * @throws IOException thrown if an error occurs with retrieving the output stream from the
     *         according data object.
     */
    OutputStream getOutputStream() throws IOException;

    /**
     * tells the location, that the earlier created output stream has been closed
     */
    void outputStreamClosed();

    /**
     * returns a writer for the according data content. If the data source does not provide a
     * writer, an adapter reader is placed on top of an output stream.
     *
     * @return the according writer
     * @throws IOException thrown if an error occurs with retrieving the writer or the underlying
     *         output stream from the according data object.
     */
    Writer getWriter() throws IOException;

    /**
     * tells the location, that the earlier created writer has been closed
     */
    void writerClosed();

}
