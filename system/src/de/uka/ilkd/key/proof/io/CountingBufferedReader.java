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

import java.io.*;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.util.ProgressMonitor;

public class CountingBufferedReader extends BufferedReader {

    private int chars;
    private int step=0;
    private ProgressMonitor monitor=ProgressMonitor.Empty.getInstance();

    public CountingBufferedReader(InputStream in) {
	super(new InputStreamReader(in, Main.DEFAULT_CHARSET));
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
	super(new InputStreamReader(in, Main.DEFAULT_CHARSET), size);
	this.step=(step == 0 ? 1 : step);
	chars=0;
    }
  
    public int read() throws IOException{
	chars++;
	if (monitor != null && chars % step==0) {
	    monitor.setProgress(chars);
	}
	return super.read();
    }

    public int getNumberOfParsedChars(){
	return chars;
    }

}