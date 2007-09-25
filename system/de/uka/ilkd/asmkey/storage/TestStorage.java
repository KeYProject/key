// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.storage;

import java.util.Arrays;

import junit.framework.Assert;
import junit.framework.TestCase;
import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.util.AsmKeYResourceManager;
import de.uka.ilkd.key.parser.ParserException;

/**
 * to test the StorageManager.
 *
 * @see StorageManager
 * @author Stanislas Nanchen
 */

public class TestStorage extends TestCase {

    private String keyhome = AsmKeYResourceManager.getInstance().getKeyHomePath();

    public void testDirectoryListing() throws StorageException {
	StorageManager manager =  new StorageManager(keyhome + "/system/resources-asmkey/tests/units");
	String[] tests = new String[] {
	    "U1.unit",
	    "U2.unit",
	    "U3.unit",
	    "U4.unit",
	    "U5.unit",
	    "U6.unit"
	};
	String[] units = manager.getUnitIds(".");
	
	Arrays.sort(units);
	Arrays.sort(tests);
	Assert.assertEquals("the array tests and units should have the same length",
			    tests.length, units.length);
	for (int i=0; i<units.length; i++) {
	    Assert.assertEquals(tests[i], units[i]);
	}
	
    }

    /**
     * the faulty units tests if the storage manager correcly raises
     * an exception when name of unit and file name do not correspond.
     */
    public void testFaultyUnits() throws StorageException {
	StorageManager faulty = new StorageManager(keyhome + "/system/resources-asmkey/tests/faulty-units");
	AstUnit[] units;
	
	try {
	    units = faulty.getUnitAstTrees(".");
	} catch (ParserException e) {
	    Assert.assertEquals("The filename in the location " + e.getLocation().getFilename() +
				" does not correspond to U2.unit",
				e.getLocation().getFilename(), "U2.unit");
	}
    }

    /**
     * tests for proof files
     */
    public void testProofFiles() throws StorageException {
	StorageManager manager =
	    new StorageManager(keyhome + "/system/resources-asmkey/tests/units");
	String[] tests = new String[] {
	    "U1.lemma1.proof",
	    "U1.lemma2.proof"
	};
	String[] proofs = manager.getAstProofIds(".", "U1");
	
	Arrays.sort(tests);
	Arrays.sort(proofs);
	Assert.assertEquals("the array tests and proofs should have the same length",
			    tests.length, proofs.length);
	for (int i=0; i<proofs.length; i++) {
	    Assert.assertEquals(tests[i], proofs[i]);
	}
    }
}
