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
import de.uka.ilkd.asmkey.unit.ImportInfo;
import de.uka.ilkd.asmkey.unit.UnitException;


/**
 * This base unit is the real Base, the first
 * file ever loaded, containing the most basic
 * things
 */
public class Base extends AbstractBaseUnit {
    
    private static Singleton singleton = null;

    private Base(AstUnit astunit) {
	super(astunit);
    }

    public ImportInfo standardImportInfo() {
	return ImportInfo.createNoSymbolsImportInfo(this);
    }

    private static Singleton getSingleton() {
	if (singleton == null) {
	    singleton = new Singleton () {
		    protected AbstractBaseUnit createInstance(AstUnit astunit) {
			return new Base(astunit);
		    }
		    
		    protected String className() {
			return "Base";
		    } 
		};
	}
	return singleton;
    }

    public static AbstractBaseUnit instance() throws UnitException {
	return getSingleton().instance();
    }

    public static void initialize(AstUnit astunit) throws UnitException {
	getSingleton().initialize(astunit);
    }

    public static void reset() {
	singleton = null;
    }

    static boolean hasBeenInitialized() {
	return getSingleton().hasBeenInitialized();
    }
    
}
