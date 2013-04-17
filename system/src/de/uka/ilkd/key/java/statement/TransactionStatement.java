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

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

public class TransactionStatement extends JavaStatement {

    public static final String[] names = { 
        "#beginJavaCardTransaction", "#commitJavaCardTransaction", "#finishJavaCardTransaction", "#abortJavaCardTransaction"
   };

    private int type;
    
    public TransactionStatement(int type) {
        super();
        if(type != de.uka.ilkd.key.java.recoderext.TransactionStatement.BEGIN && type != de.uka.ilkd.key.java.recoderext.TransactionStatement.COMMIT 
             && type != de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH && type != de.uka.ilkd.key.java.recoderext.TransactionStatement.ABORT) {
            throw new IllegalArgumentException("Wrong transaction statement type "+type);
        }
        this.type = type;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnTransactionStatement(this);
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    public void prettyPrint(de.uka.ilkd.key.java.PrettyPrinter p) throws java.io.IOException {
        p.printTransactionStatement(this);
    }
    
    public int getPrecedence() {
        return 13;
    }
    
    public String toString() {
        return names[type - 1];
    }
    
    public boolean equals(Object o) {
        if (o != null && o instanceof TransactionStatement) {
            return ((TransactionStatement)o).type == this.type;
        }
        return false;
    }


    public MatchConditions match(SourceData source, MatchConditions conditions) {
        if(this.equals(source.getSource())) {
            source.next();
            return conditions;
        }
        return null;
    }
    
    public boolean equalsModRenaming(SourceElement source, NameAbstractionTable nat) {
        return this.equals(source);
    }


}