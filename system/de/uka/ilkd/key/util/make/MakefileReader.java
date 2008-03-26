// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util.make;
import java.io.File;
import java.io.FileReader;
import java.util.HashSet;

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
	    while (fr.read()!=(int)'\n') {	    
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
		if (read==(int)'\n' || read==(int)'\r') {
		    readStr="";
		} else if (read==(int)'\t') {
		    readStr="";
		    gotoNextLine(fr);
		} else {
		    if (read!=(int)':') {
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
	hset = new HashSet<String>();
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
