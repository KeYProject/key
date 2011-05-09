package de.uka.ilkd.key.java.recoderext.ldt;

import recoder.java.*;
import recoder.java.expression.Operator;
import recoder.java.reference.*;


/**
 * Represents the range suffix for subsequences written in suffix notation, e.g., <pre>seq[from..to]</pre>
 * @since 1.7.2119
 * @author bruns
 *
 */
public class SeqSubRangeSuffix extends Operator {
    
    private Expression from;
    private Expression to;
    
    public SeqSubRangeSuffix (Expression fromIdx, Expression toIdx){
        from = fromIdx;
        to = toIdx;
        makeParentRoleValid();
    }


    @Override
    public Expression getChildAt(int arg0) {
        switch (arg0) {
        case 0: return from;
        case 1: return to;
        default: throw new IndexOutOfBoundsException("A range suffix has only children 0 and 1, not "+arg0);
        }
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public int getChildPositionCode(ProgramElement arg0) {
        if (arg0.equals(from))
            return 0;
        if (arg0.equals(to))
            return 1;
        return -1;
    }

    @Override
    public boolean replaceChild(ProgramElement arg0, ProgramElement arg1) {
        if (arg1 instanceof Expression){
            final Expression ex = (Expression) arg1;
            switch (getChildPositionCode(arg0)) {
            case 0: from = ex;
            return true;
            case 1: to = ex;
            return true;
            }
        }
        return false;
    }

    @Override
    public void accept(SourceVisitor arg0) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public SeqSubRangeSuffix deepClone() {
        return new SeqSubRangeSuffix(from.deepClone(), to.deepClone());
    }
    
    @Override
    public String toString(){
        return "["+from+".."+to+"]";
    }


    @Override
    public int getArity() {
        return 2;
    }


    @Override
    public int getNotation() {
        return INFIX;
    }


    @Override
    public int getPrecedence() {
        return 1;
    }
    
}