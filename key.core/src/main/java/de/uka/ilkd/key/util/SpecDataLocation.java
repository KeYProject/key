/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.Reader;
import java.io.Writer;

import recoder.io.DataLocation;


public class SpecDataLocation implements DataLocation {

    /** unknown location (e.g. if the location does not denote a file) */
    public static final DataLocation UNKNOWN_LOCATION = new SpecDataLocation("UNKNOWN", "unknown");

    final String type;

    final String location;

    public SpecDataLocation(String type, String location) {
        this.type = type;
        this.location = location;
    }

    public InputStream getInputStream() throws IOException {
        throw new UnsupportedOperationException("getInputStream not supported");
    }

    public OutputStream getOutputStream() throws IOException {
        throw new UnsupportedOperationException("getInputStream not supported");
    }

    public Reader getReader() throws IOException {
        throw new UnsupportedOperationException("getInputStream not supported");
    }

    public String getType() {
        return type;
    }

    public Writer getWriter() throws IOException {
        throw new UnsupportedOperationException("getInputStream not supported");
    }

    public boolean hasReaderSupport() {
        return false;
    }

    public boolean hasWriterSupport() {
        return false;
    }

    public void inputStreamClosed() {
    }

    public boolean isWritable() {
        return false;
    }

    public void outputStreamClosed() {
    }

    public void readerClosed() {
    }

    public void writerClosed() {
    }

    public String toString() {
        return type + ":" + location;
    }

}
