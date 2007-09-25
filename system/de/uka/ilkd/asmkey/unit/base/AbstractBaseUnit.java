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
import de.uka.ilkd.asmkey.unit.Unit;
import de.uka.ilkd.key.logic.Name;


/**
 * This class is an extension of 
 * Unit and deals with the base files that
 * contains builtin sorts and axioms, and
 * properties of derived predicates.
 */
public abstract class AbstractBaseUnit extends Unit {

    AbstractBaseUnit(Name name) {
	super(name);
    }

    public AbstractBaseUnit(AstUnit astunit) {
	super(astunit);
    }

    public abstract ImportInfo standardImportInfo();
    
}
