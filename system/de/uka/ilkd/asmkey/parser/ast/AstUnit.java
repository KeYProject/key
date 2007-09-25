// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.asmkey.parser.ast;

import de.uka.ilkd.asmkey.util.ArrayUtil;
import de.uka.ilkd.key.parser.Location;

/**
 * Instances of this class contains all the ast declarations
 * for a given unit.
 */
public class AstUnit extends AstNode {
    
    private Identifier unit;
    private AstExport export;
    private AstImport[] imports;
    private AstUnitDeclarations decls;

    AstUnit(Location location, Identifier unit, AstExport export, AstImport[] imports,
	    AstUnitDeclarations decls) {
	super(location);
	this.unit = unit;
	this.export = export;
	this.imports = imports;
	this.decls = decls;
    }

    public Identifier getUnitId() {
	return unit;
    }
    
    public AstExport getExport() {
	return export;
    }

    public AstImport[] getImports() {
	return imports;
    }
    
    public AstUnitDeclarations getDeclarations() {
	return decls;
    }

    /** for debug only */
    public String toString() {
	return "[AstUnit:u=" + unit + ";imports=" + ArrayUtil.toString(imports) 
	    + ";decls=" + decls + "]";
    }
}
