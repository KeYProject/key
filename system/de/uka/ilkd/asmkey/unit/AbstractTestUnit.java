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

import java.io.IOException;

import junit.framework.Assert;
import de.uka.ilkd.asmkey.logic.DerivedFunction;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParserFactory;
import de.uka.ilkd.asmkey.storage.StorageException;
import de.uka.ilkd.asmkey.storage.StorageManager;
import de.uka.ilkd.asmkey.util.TestUtil;
import de.uka.ilkd.key.parser.ParserException;

/**
 * to test the unit manager
 */
public abstract class AbstractTestUnit extends TestUtil {
    
    protected StorageManager storage;
    protected UnitManager manager;
    protected UnitListener listener;
    
    protected abstract UnitListener listener() throws IOException;
    protected abstract DeclarationParserFactory factory();


    public void setUp() throws StorageException, IOException {
	storage = new StorageManager(keyhome + "/system/resources-asmkey/tests/units");
	listener = listener();
	manager = new UnitManager(storage, listener, factory(), ".", null);
	listener.beginLogging();
    }

    // public void tearDown() {
// 	manager.resetBaseUnits();
//     }

    public void managerLoad() {
	try {
	    manager.loadUnits();
	} catch (ParserException e) {
	    Assert.fail(testName() + ":ParserException caught: " + e.getMessage() +
			" at location: " + (e.getLocation()==null?"":e.getLocation().toString()));
	} catch (UnitException e) {
	    Assert.fail(testName() + ":UnitException caught: " + e.getMessage());
	}
    }

    public abstract class Tester {

	public abstract Unit unit();

	public abstract String message();
	
	public abstract boolean test(DerivedFunction f);
	
    }

    public abstract String testName();

}
