/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.Reader;
import java.io.Writer;
import java.net.URL;
import java.nio.charset.StandardCharsets;

import recoder.io.DataLocation;

/**
 * This class implements a data location, that describes an arbitrary URL. It is read-only and uses
 * the URL's own stream for reading
 *
 * @author mulbrich
 * @since 2006-11-02
 */
public class URLDataLocation implements DataLocation {

    private final URL url;

    public static final String LOCATION_TYPE_FILE = "URL";

    public URLDataLocation(URL url) {
        this.url = url;
    }

    /**
     * return the URL's input stream
     *
     * @see recoder.io.DataLocation#getInputStream()
     */
    public InputStream getInputStream() throws IOException {
        return url.openStream();
    }

    /**
     * @throws UnsupportedOperationException always
     * @see recoder.io.DataLocation#getOutputStream()
     */
    public OutputStream getOutputStream() throws IOException {
        throw new UnsupportedOperationException("Output is not supported for URLDataLocation");
    }

    /**
     * @throws UnsupportedOperationException always
     * @see recoder.io.DataLocation#getWriter()
     */
    public Writer getWriter() throws IOException {
        throw new UnsupportedOperationException("Output is not supported for URLDataLocation");
    }

    public Reader getReader() throws IOException {
        return new InputStreamReader(getInputStream(), StandardCharsets.UTF_8);
    }

    public String getType() {
        return LOCATION_TYPE_FILE;
    }

    /**
     * Getter for url.
     *
     * @return the url of this data location
     */
    public URL getUrl() {
        return url;
    }

    public String toString() {
        return getType() + ":" + url;
    }

    public boolean hasReaderSupport() {
        return true;
    }

    public boolean hasWriterSupport() {
        return false;
    }

    public boolean isWritable() {
        return false;
    }

    public void inputStreamClosed() {
    }

    public void outputStreamClosed() {
    }

    public void readerClosed() {
    }

    public void writerClosed() {
    }

}
