// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.unit.base;

import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.unit.UnitException;

/**
 * this class serves as instance in the singleton classes, it mixes
 * the singleton and delegates patterns.  {@link Base}, {@link Bool},
 * {@link Int} and {@link Sequence}
 */
public abstract class Singleton {

    private AbstractBaseUnit instance;

    protected Singleton() {
	super();
    }
    
    public AbstractBaseUnit instance() throws UnitException {
	if (instance == null) {
	    throw new UnitException(className() +
				    ":the instance has not been initialized");
	}
	return instance;
    }
    
    public void initialize(AstUnit astunit) throws UnitException {
	if (instance == null) {
	    instance = createInstance(astunit);
	} else {
	    throw new UnitException(className() +
				    ":the instance has already been initialized.");
	}
    }

    boolean hasBeenInitialized() {
	return instance != null;
    }

    protected abstract AbstractBaseUnit createInstance(AstUnit astunit);

    protected abstract String className();


}
