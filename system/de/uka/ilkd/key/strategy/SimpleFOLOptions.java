// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Name;


public abstract class SimpleFOLOptions {
    
    protected final static String BASE_NAME = "Simple FOL";
    
    public abstract Name name ();

    public boolean gamma () {
        return false;
    }

    public boolean test () {
        return false;
    }

    public static final SimpleFOLOptions FOL =
        new SimpleFOLOptions () {
            public Name name () {
		return new Name(BASE_NAME);
            }

	    public boolean gamma () {
		return true;
	    }
        };
    
    public static final SimpleFOLOptions TEST =
        new SimpleFOLOptions () {
            public Name name () {
		return new Name(BASE_NAME+" for unit test generation");
            }

	    public boolean test () {
		return true;
	    }
        };
    

}
