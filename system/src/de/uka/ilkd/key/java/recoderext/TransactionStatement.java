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

package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.statement.JavaStatement;

public class TransactionStatement extends JavaStatement {

    private static final long serialVersionUID = -4470827742145010769L;

    public static final int BEGIN = 1; 
    public static final int COMMIT = 2; 
    public static final int FINISH = 3; 
    public static final int ABORT = 4;
    
    private int type;
    
    public TransactionStatement(int type) {
        super();
        if(type != BEGIN && type != COMMIT && type != FINISH && type != ABORT) {
            throw new IllegalArgumentException("Wrong transaction statement type "+type);
        }
        this.type = type;
        makeParentRoleValid();
    }
    
    protected TransactionStatement(TransactionStatement proto) {
        this(proto.type);
    }

    public int getType() {
        return type;
    }
    
    public recoder.java.ProgramElement getChildAt(int index) {
        return null;
    }


    @Override
    public Statement deepClone() {
        return new TransactionStatement(this);
    }
    
    @Override
    public void accept(SourceVisitor sourceVisitor) {
    }


    @Override
    public int getChildCount() {
        return 0;
    }


    @Override
    public int getChildPositionCode(recoder.java.ProgramElement arg0) {
        return 0;
    }

    @Override
    public boolean replaceChild(recoder.java.ProgramElement arg0,
            recoder.java.ProgramElement arg1) {
        return false;
    }
    
    public boolean equals(Object o) {
        if (o != null && o instanceof TransactionStatement) {
            return ((TransactionStatement)o).type == this.type;
        }
        return false;
    }
    
    public int hashCode() {
        return type;
    }

    public String toString() {
        return de.uka.ilkd.key.java.statement.TransactionStatement.names[type - 1];
    }

}