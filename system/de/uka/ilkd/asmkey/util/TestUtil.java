// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.util;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;

/** some goodies for tests */
public class TestUtil extends TestCase {

    /** dummy class that implements the Named interface */
    public static class Item implements Named {

	private Name name;

	public Item(String name) {
	    this.name = new Name(name);
	}

	public Name name() {
	    return name;
	}

	public String toString() {
	    return name.toString();
	}
    }

    /* --- code for loading test material from files. --- */	
    
    protected final String keyhome = AsmKeYResourceManager.getInstance().getKeyHomePath();

    protected String[] getLines(String filename) throws IOException {
	BufferedReader in =
	    new BufferedReader
	    (new FileReader(keyhome + "/system/resources-asmkey/tests/testutil/" + filename));
	List list = new ArrayList();
	String line;
	
	while((line = in.readLine()) != null) {
	    line = line.trim();
	    if (!line.equals("") && !line.startsWith("//")) {
		list.add(line);
	    }
	}
	return ((String[]) list.toArray(new String[list.size()]));
    }


}
