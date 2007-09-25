// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;

import java.io.*;

/**
 * this class implements the {@link UnitListener} interface
 * and output logging activity under a text form in a file
 * or in the standart output.
 */	
public class TextUnitListener implements UnitListener {

    private int majorTotal;
    private int majorCurrent;
    
    private int minorTotal;
    private int minorCurrent;

    private boolean active;
    private boolean pause;
    private boolean stopped;

    private PrintStream out;
    private FileOutputStream file;

    private TextUnitListener(PrintStream out, FileOutputStream file) {
	this.out = out;
	this.file = file;
	this.majorTotal = 0;
	this.majorCurrent = 0;
	this.minorTotal = 0;
	this.minorCurrent = 0;
	this.active = false;
	this.pause = false;
	this.stopped = false;
    }

    private TextUnitListener(FileOutputStream file) {
	this(new PrintStream(file), file);
    }

    private TextUnitListener(PrintStream out) {
	this(out, null);
    }
    
    public void beginLogging() {
	if (!stopped) {
	    if (pause) {
		out.println("--- log pause off ---");
	    } else {
		out.println("--- begin logging ---");
	    }
	    this.active = true;
	    this.pause = false;
	}
    }

    public void pauseLogging() {
	out.println("--- log pause on ---");
	this.active = false;
	this.pause = true;
	this.majorTotal = 0;
	this.minorTotal = 0;
    }
    
    public void stopLogging() {
	out.println("--- end logging --- ");
	this.active = false;
	this.pause = false;
	this.stopped = true;
	this.majorTotal = 0;
	this.minorTotal = 0;
	if (file != null) {
	    try {
		file.close();
	    } catch(IOException e) {}
	}
    }
    
    public void loadingInitialLogEntry(String message, int major) {
	if (active) {
	    this.majorCurrent = 0;
	    this.majorTotal = major;
	    this.minorTotal = 0;
	    out.println(message);
	}
    }
    
    public void loadingMajorLogEntry(String message, int minor) {
	if (active) {
	    majorCurrent = increment(majorCurrent, majorTotal);
	    this.minorTotal = minor;
	    this.minorCurrent = 0;
	    out.println(Integer.toString(majorCurrent) + ". " + message);
	}
    }

    public void loadingMajorLogEntry(String message) {
	if (active) {
	    loadingMajorLogEntry(message, 0);
	}
    }

    public void loadingMinorLogEntry(String message) {
	if (active) {
	    minorCurrent = increment(minorCurrent, minorTotal);
	    out.println(minorTab + Integer.toString(minorCurrent) + ". " + message);
	}
    }

    public void operationLogEntry(String message) {
	if (active) {
	    out.println("A. " + message);
	}
    }

    private final int increment(int current, int total) {
	return (current<total)?current+1:total;
    }

    /* --- static part --- */

    static private final String minorTab = "   ";

    public static final TextUnitListener fileUnitListener(File file) throws IOException {
	return new TextUnitListener(new FileOutputStream(file));
    }

    public static final TextUnitListener stdOutUnitListener() {
	return stdUnitListener(FileDescriptor.out);
    }

    public static final TextUnitListener stdErrUnitListener() {
	return stdUnitListener(FileDescriptor.err);
    }

    private static final TextUnitListener stdUnitListener(FileDescriptor desc) {
	return new TextUnitListener(new PrintStream(new FileOutputStream(desc), true));
    }
}
