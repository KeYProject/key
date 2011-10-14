package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;

public class TransactionStatement extends JavaStatement {

    private static final String[] names = { 
        "#beginJavaCardTransaction", "#commitJavaCardTransaction", "#abortJavaCardTransaction"
   };

    private int type;
    
    public TransactionStatement(int type) {
        super();
        if(type != de.uka.ilkd.key.java.recoderext.TransactionStatement.BEGIN &&
                  type != de.uka.ilkd.key.java.recoderext.TransactionStatement.COMMIT && type != de.uka.ilkd.key.java.recoderext.TransactionStatement.ABORT) {
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
    
    public String toString() {
        return names[type - 1];
    }

}
