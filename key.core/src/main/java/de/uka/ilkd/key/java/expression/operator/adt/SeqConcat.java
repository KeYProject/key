package de.uka.ilkd.key.java.expression.operator.adt;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.visitor.Visitor;

public class SeqConcat extends BinaryOperator {

    public SeqConcat(ExtList children) {
        super(children);
    }


    public SeqConcat(Expression seq1, Expression seq2) {
        super(seq1, seq2);
    }


    public int getPrecedence() {
        return 0;
    }


    public int getNotation() {
        return PREFIX;
    }


    public void visit(Visitor v) {
        v.performActionOnSeqConcat(this);
    }


    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printSeqConcat(this);
    }

}
