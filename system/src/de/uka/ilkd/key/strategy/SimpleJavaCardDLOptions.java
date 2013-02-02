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


package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Name;


/**
 * Parametrize the strategy Simple JavaCardDL to get rid of that messy class
 * hierarchy. Someone write a GUI for this class ...
 */
public abstract class SimpleJavaCardDLOptions {
    
    protected final static String BASE_NAME = "Simple JavaCardDL";
    
    public abstract Name name ();

    public boolean useMethodContracts () {
        return false;
    }

    public boolean unwindLoops () {
        return false;
    }

    public boolean expandMethods () {
        return false;
    }

    public boolean test(){
	return false;
    }

    public static final SimpleJavaCardDLOptions NOTHING =
        new SimpleJavaCardDLOptions () {
            public Name name () {
                return new Name ( BASE_NAME
                                  + " without expanding loops and method bodies" );
            }
        };
    
    public static final SimpleJavaCardDLOptions LOOPS =
        new SimpleJavaCardDLOptions () {
	    public boolean unwindLoops () { return true; }
            public Name name () {
                return new Name ( BASE_NAME
                                  + " without expanding method bodies" );
            }
        };

    public static final SimpleJavaCardDLOptions GAMMA_LOOPS_METHODS =
        new SimpleJavaCardDLOptions () {
	    public boolean test () { return true; }
	    public boolean unwindLoops () { return true; }
	    public boolean expandMethods () { return true; }
            public Name name () {
                return new Name ( BASE_NAME
                                  + " for Unit Test Generation " );
            }
        };
    
    public static final SimpleJavaCardDLOptions LOOPS_METHODS =
        new SimpleJavaCardDLOptions () {
	    public boolean unwindLoops () { return true; }
	    public boolean expandMethods () { return true; }
            public Name name () {
                return new Name ( BASE_NAME );
            }
        };
    
    public static final SimpleJavaCardDLOptions METHODS =
        new SimpleJavaCardDLOptions () {
	    public boolean expandMethods () { return true; }
            public Name name () {
                return new Name ( BASE_NAME
                                  + " without unwinding loops" );
            }
        };

    public static final SimpleJavaCardDLOptions CONTRACTS =
        new SimpleJavaCardDLOptions () {
	    public boolean useMethodContracts () { return true; }
            public Name name () {
                return new Name ( BASE_NAME
                                  + " Using Method Contracts without "
                                  + "expanding loops and method bodies" );
            }
        };
    
    public static final SimpleJavaCardDLOptions CONTRACTS_LOOPS =
        new SimpleJavaCardDLOptions () {
	    public boolean unwindLoops () { return true; }
	    public boolean useMethodContracts () { return true; }
            public Name name () {
                return new Name ( BASE_NAME
                                  + " Using Method Contracts without "
                                  + "expanding method bodies" );
            }
        };
    
    public static final SimpleJavaCardDLOptions CONTRACTS_METHODS =
        new SimpleJavaCardDLOptions () {
	    public boolean expandMethods () { return true; }
	    public boolean useMethodContracts () { return true; }
            public Name name () {
                return new Name ( BASE_NAME
                                  + " Using Method Contracts without "
                                  + "unwinding loops" );
            }
        };
    
    public static final SimpleJavaCardDLOptions CONTRACTS_LOOPS_METHODS =
        new SimpleJavaCardDLOptions () {
	    public boolean expandMethods () { return true; }
	    public boolean useMethodContracts () { return true; }
	    public boolean unwindLoops () { return true; }
            public Name name () {
                return new Name ( BASE_NAME
                                  + " Using Method Contracts" );
            }
        };
    
    
}
