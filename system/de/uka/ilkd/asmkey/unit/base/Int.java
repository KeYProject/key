// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.unit.base;

import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.unit.ImportInfo;
import de.uka.ilkd.asmkey.unit.UnitException;
import de.uka.ilkd.key.logic.Name;

/** This base unit is responsible
 * for loading the rules, functions, etc..
 * for integers.
 *
 * @author Stanislas Nanchen 
 */

public class Int extends AbstractBaseUnit {

    private static Singleton singleton = null;
    private static Name builtInName = new Name("Int.int");

    private Int(AstUnit astunit) {
	super(astunit);
    }

    public ImportInfo standardImportInfo() {
	return ImportInfo.createAllSymbolsImportInfo(this);
    }

    private static Singleton getSingleton() {
	if (singleton == null) {
	    singleton = new Singleton () {
		    protected AbstractBaseUnit createInstance(AstUnit astunit) {
			return new Int(astunit);
		    }
		    
		    protected String className() {
			return "Int";
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

    public static Name builtInName() {
	return builtInName;
    }

    static boolean hasBeenInitialized() {
	return getSingleton().hasBeenInitialized();
    }

}
