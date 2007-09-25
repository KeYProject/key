// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit.base;

import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParserFactory;
import de.uka.ilkd.asmkey.storage.StorageException;
import de.uka.ilkd.asmkey.storage.StorageManager;
import de.uka.ilkd.asmkey.unit.*;
import de.uka.ilkd.key.parser.ParserException;


/** This class is responsible for loading the base units, that
 * form the central library.
 * we use a second graph; library and user defined units are
 * separate and all exported base symbols are imported (import all)
 */
public class BaseUnitParser extends AbstractUnitParser {

    public BaseUnitParser(UnitManager manager,
			  UnitListener listener,
			  UnitGraph graph,
			  StorageManager storage,
			  DeclarationParserFactory factory) {
	super(manager, listener, graph, storage, factory, null);
    }
    
    public BaseUnitParser(UnitManager manager,
			  UnitListener listener,
			  UnitGraph graph,
			  StorageManager storage) {
	super(manager, listener, graph, storage, null);
    }

    public AstUnit[] getAstUnits() throws ParserException, StorageException {
	return storage.getBaseUnitAstTrees();
    }

    public Unit createUnit(AstUnit astunit) throws UnitException {
	String id = astunit.getUnitId().getText();
	if (id.equals("Bool")) {
	    Bool.initialize(astunit);
	    return Bool.instance();
	} else if (id.equals("Int")) {
	    Int.initialize(astunit);
	    return Int.instance();
	} else if (id.equals("Sequence")) {
	    Sequence.initialize(astunit);
	    return Sequence.instance();
	} else if (id.equals("Base")) {
	    Base.initialize(astunit);
	    return Base.instance();
	} else if (BaseUnit.isOtherBaseUnit(id)) {
	    return new BaseUnit(astunit);
	} else {
	    throw new UnitException("The <base> unit with id=" + id + 
				    " does not belong to the standart library");
	}
    }

    public void postParsing() throws UnitException {
	if (!Base.hasBeenInitialized()) {
	    throw new UnitException("BaseUnit Base not initialized.");
	}
	if (!Bool.hasBeenInitialized()) {
	    throw new UnitException("BaseUnit Bool not initialized.");
	}
	if (!Int.hasBeenInitialized()) {
	    throw new UnitException("BaseUnit Int not initialized.");
	}
	if (!Sequence.hasBeenInitialized()) {
	    throw new UnitException("BaseUnit Sequence not initialized.");
	}
    }
    
}
