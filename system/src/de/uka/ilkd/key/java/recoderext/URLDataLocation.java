// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext;

import java.io.*;
import java.net.URL;

import recoder.io.DataLocation;

/**
 * This class implements a data location, that describes an arbitrary URL. It is read-only
 * and uses the URL's own stream for reading
 * 
 * @author mulbrich
 * @since 2006-11-02
 */
public class URLDataLocation implements DataLocation {

    private URL url;
    
    public static final String LOCATION_TYPE_FILE = "URL";

    public URLDataLocation(URL url) {
        this.url = url;
    }

    /** 
     * return the URL's input stream
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
        return new InputStreamReader(getInputStream());
    }

    public String getType() {
        return LOCATION_TYPE_FILE;
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