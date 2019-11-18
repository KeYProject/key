// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.statement.Catch;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class CatchSVWrapper extends Catch 
    implements KeYRecoderExtension, SVWrapper{
   
    /**
     * 
     */
    private static final long serialVersionUID = 6288254708744002494L;
    protected SchemaVariable sv;

    public CatchSVWrapper(SchemaVariable sv) {
	this.sv=sv;
    }


    /**
     * sets the schema variable of sort statement
     * @param sv the SchemaVariable
     */
    public void setSV(SchemaVariable sv) {
	this.sv=sv;
    }

    /**
     * returns a String name of this meta construct.
     */
    public SchemaVariable getSV() {
	return sv;
    }

    public void accept(SourceVisitor v) {
	v.visitIdentifier(new Identifier(sv.name().toString()));
    }
    
    public CatchSVWrapper deepClone() {
	return new CatchSVWrapper(sv);
    }

    public int getChildCount() {
	return 0;
    }

    public ProgramElement getChildAt(int i) {
	throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(recoder.java.ProgramElement pe) {
	throw new ArrayIndexOutOfBoundsException();
    }

    public boolean replaceChild(recoder.java.ProgramElement p1, 
				recoder.java.ProgramElement p2) {
	return false;
    }

    public int getStatementCount() {
	return 0;
    }
    
    public recoder.java.Statement getStatementAt(int s) {
	throw new ArrayIndexOutOfBoundsException();
    }


}