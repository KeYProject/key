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


/** This class implements the booleans for ASMKeY. It is
 * used in the InitConfig of asmkey. most of the code is
 * from the key booleanLDT.
 *
 * @see de.uka.ilkd.asmkey.proof.init.InitConfig
 * @author Stanislas Nanchen 
 */ 

public class Bool extends AbstractBaseUnit {
    
    private static Singleton singleton = null;

    private static final Name builtInName = new Name("Bool.bool");
    private static final Name[] builtInConsts = new Name[]
	{
	    new Name("Bool.true"),
	    new Name("Bool.false")
	};

    /** the boolean literals as function symbols and terms */
//     private Function bool_true;
//     private Term term_bool_true;
//     private Function bool_false;
//     private Term term_bool_false;
    
    private Bool(AstUnit astunit) {
	super(astunit);
    }

    public ImportInfo standardImportInfo() {
	return ImportInfo.createAllSymbolsImportInfo(this);
    }

//     public void init(Namespace func_ns, Sort targetSort, ListOfType type) {
// 	super.init(func_ns, targetSort, type);

// 	// the literals
// 	/*bool_true  = addFunction((Function) func_ns.lookup(new Name("TRUE")));
// 	term_bool_true  = TermFactory.DEFAULT.createFunctionTerm(bool_true);
// 	bool_false = addFunction((Function) func_ns.lookup(new Name("FALSE")));
// 	term_bool_false  = TermFactory.DEFAULT.createFunctionTerm(bool_false);*/
	
//     }

    private static Singleton getSingleton() {
	if (singleton == null) {
	    singleton = new Singleton () {
		    protected AbstractBaseUnit createInstance(AstUnit astunit) {
			return new Bool(astunit);
		    }
		    
		    protected String className() {
			return "Bool";
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

    public static Name[] builtInConsts() {
	return builtInConsts;
    }

    static boolean hasBeenInitialized() {
	return getSingleton().hasBeenInitialized();
    }

}
