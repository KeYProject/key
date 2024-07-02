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

package de.uka.ilkd.key.proof.io;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.util.ProgressMonitor;

public class CountingBufferedReader extends BufferedReader {

    private int chars;
    private int step=0;
    private ProgressMonitor monitor=ProgressMonitor.Empty.getInstance();

    public CountingBufferedReader(InputStream in) {
	super(new InputStreamReader(in, IOUtil.DEFAULT_CHARSET));
	chars = 0;
	step  = 1;
    }

    public CountingBufferedReader(InputStream in, 
				       ProgressMonitor monitor, 
				       int step) {
	this(in);
	this.step=(step == 0 ? 1 : step);
	this.monitor=monitor;
	chars=0;
    }

    public CountingBufferedReader(InputStream in, 
				       ProgressMonitor monitor, 
				       int step, int alreadyRead) {
	this(in, monitor, step);
	chars = alreadyRead;
    }

    public CountingBufferedReader(InputStream in, int size, int step) {
	super(new InputStreamReader(in, IOUtil.DEFAULT_CHARSET), size);
	this.step=(step == 0 ? 1 : step);
	chars=0;
    }
  
    private void incCharCounter(long inc) {
        chars += inc;
        if (monitor != null && chars % step==0) {
            monitor.setProgress(chars);
        }
    }
    
    @Override
    public int read() throws IOException{
       final int readChar = super.read();
       if (readChar != -1) incCharCounter(1);
       return readChar; 
    }
    
    @Override
    public int read(char cbuf[], int off, int len) throws IOException {
        final int readChars = super.read(cbuf, off, len); 
        if (readChars > 0) incCharCounter(readChars);
        return readChars;
    }

    @Override
    public String readLine() throws IOException {
        final String line = super.readLine();
        if (line != null) incCharCounter(line.length());
        return line;
    }
 
    @Override
    public long skip(long n) throws IOException {
        final long skippedChars = super.skip(n);
        if (skippedChars > 0) incCharCounter(skippedChars);
        return skippedChars;
    }
    

    public int getNumberOfParsedChars(){
	return chars;
    }

}