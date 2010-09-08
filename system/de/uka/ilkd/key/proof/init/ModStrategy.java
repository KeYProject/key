// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.init;

/** Describes if the parts of an initial configuration are to be modified
 * or not when reading input to the prover.
 */
public class ModStrategy {

    /** A constant strategy modifying always */
    public static final ModStrategy MOD_ALL=new ModStrategy();
    /** A strategy modifying everything except variables*/
    public static final ModStrategy NO_VARS=new ModStrategy() {
	    public boolean modifyVariables() {return false;}
	};

    /** A strategy modifying everything except variables and generic sorts*/
    public static final ModStrategy NO_VARS_GENSORTS=new ModStrategy() {
        public boolean modifyVariables() {return false;}
        public boolean modifyGenericSorts() {return false;}
    };

    /** A strategy modifying everything except generic sorts*/
    public static final ModStrategy NO_GENSORTS=new ModStrategy() {
        public boolean modifyGenericSorts() {return false;}
    };

    /** A strategy modifying everything except variables and functions*/
    public static final ModStrategy NO_VARS_FUNCS=new ModStrategy() {
	    public boolean modifyVariables() {return false;}
	    public boolean modifyProgramVariables() {return false;}
	    public boolean modifyFunctions() {return false;}
	};

    /** A strategy modifying everything except variables, functions and generic sorts*/
    public static final ModStrategy NO_VARS_FUNCS_GENSORTS=new ModStrategy() {
            public boolean modifyVariables() {return false;}
            public boolean modifyProgramVariables() {return false;}
            public boolean modifyFunctions() {return false;}
            public boolean modifyGenericSorts() {return false;}
        };

    /** A strategy modifying everything except functions*/
    public static final ModStrategy NO_FUNCS=new ModStrategy() {
            public boolean modifyProgramVariables() {return false;}
	    public boolean modifyFunctions() {return false;}
	};

    /** returns true iff the heuristics namespace should be modified*/
    public boolean modifyHeuristics() {
	return true;
    }

    /**
     * returns true iff the sorts namespace should be modified concerning
     * concrete sorts
     */
    public boolean modifySorts() {
	return true;
    }

    /**
     * returns true iff the sorts namespace should be modified concerning
     * generic sorts
     */
    public boolean modifyGenericSorts() {
        return true;
    }

    /** returns true iff the variable namespace should be modified*/
    public boolean modifyVariables() {
	return true;
    }

    /** returns true iff the variable namespace should be modified*/
    public boolean modifyProgramVariables() {
	return true;
    }

    /** returns true iff the functions namespace should be modified*/
    public boolean modifyFunctions() {
	return true;
    }

    /** returns true iff the choice namespace should be modified*/
    public boolean modifyChoices() {
	return true;
    }

    /** returns true iff the java model info  should be modified*/
    public boolean modifyJavaInfo() {
	return true;
    }
}
