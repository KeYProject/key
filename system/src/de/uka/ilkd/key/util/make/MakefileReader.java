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


package de.uka.ilkd.key.util.make;
import java.io.File;
import java.io.FileReader;
import java.util.HashSet;
import java.util.LinkedHashSet;

public class MakefileReader {

    /** stores found rules */
    private HashSet<String> hset;

    /** the makefile */
    private File file;

    public MakefileReader(File file) {
	this.file = file;
    }


    private void gotoNextLine(FileReader fr) {
	try {
	    while (fr.read()!='\n') {	    
	    }
	} catch (Exception e) {
	    System.out.println("Error reading file.");
	}	
    }

    private void read(FileReader fr) {
	try {
	    String readStr = "";
	    int read = fr.read();
	    while (read!=-1) {
		if (read=='\n' || read=='\r') {
		    readStr="";
		} else if (read=='\t') {
		    readStr="";
		    gotoNextLine(fr);
		} else {
		    if (read!=':') {
			readStr=readStr+(char)read;		
		    } else {
			hset.add(readStr);
			readStr="";
			gotoNextLine(fr);
		    }
		} 
		read = fr.read();
	    }
	} catch (Exception e) {
	    System.err.println("Error reading file.");
	}		
    }
    
    public HashSet<String> getRules() {
	hset = new LinkedHashSet<String>();
	try {
	    FileReader fr = new FileReader(file);		
	    if (hset.size()==0) read(fr);
	    fr.close();
	} catch (Exception e) {
	    // if does not exist => empty hashset
	    System.out.println("No rules exist. Will create new ones...");
	}
	return hset;
    }

    public static void main(String[] args) {
	HashSet<String> set=new MakefileReader(new File(args[0])).getRules();
	System.out.println("Read "+set.size()+" rules.");
    }

}
