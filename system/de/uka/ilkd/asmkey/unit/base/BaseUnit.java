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

import java.util.HashSet;

import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.unit.ImportInfo;
import de.uka.ilkd.key.logic.Name;


/**
 * This class is an extension of 
 * Unit and deals with the base files that
 * contains builtin sorts and axioms, and
 * properties of derived predicates.
 */
public class BaseUnit extends AbstractBaseUnit {

    private final ImportInfo info;

    BaseUnit(Name name) {
	super(name);
	info = ImportInfo.createNoSymbolsImportInfo(this);
    }

    public BaseUnit(AstUnit astunit) {
	super(astunit);
	info = ImportInfo.createAllSymbolsImportInfo(this);
    }

    public ImportInfo standardImportInfo() {
	return info;
    }
    
    private static final HashSet base;

    static {
	base = new HashSet();
	base.add("FOL");
	base.add("Modal");
	base.add("Asm");
	base.add("Def");
	base.add("Upd");
	base.add("Con");
	base.add("Acc");
	base.add("Equi");
    }

    public static boolean isOtherBaseUnit(String id) {
	return base.contains(id);
    }

}
