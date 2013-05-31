// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.util;

import java.io.*;

import recoder.io.DataLocation;


public class SpecDataLocation implements DataLocation {

    public static final DataLocation UNKNOWN_LOCATION = new SpecDataLocation("UNKNOWN", "");

    String type;

    String location;

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
        return type + "://" + location;
    }

}
