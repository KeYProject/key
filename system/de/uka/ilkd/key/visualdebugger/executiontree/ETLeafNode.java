package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.visualdebugger.SourceElementId;

public class ETLeafNode extends ETNode {
    private int state;

    private String exceptionName = null;

    private SourceElementId programCounter = null;

    private SourceElementId expression = null;

    // surround with try catch

    public static int TERMINATED = 1;

    public static int INFEASIBLE = 2;

    public static int SUSPENDED = 3;// depr

    // public ETLeafNode(ListOfTerm bc, int st){
    // super(bc);
    // this.state = st;
    // assert(st==TERMINATED || st==INFEASIBLE|| st== SUSPENDED) ;
    // }

    public ETLeafNode(ListOfTerm bc, int st, ETNode parent) {
        super(bc, parent);
        this.state = st;
        assert (st == TERMINATED || st == INFEASIBLE || st == SUSPENDED);
    }

    public ETLeafNode(ListOfTerm bc, int st, LinkedList nodes, ETNode parent) {
        super(bc, nodes, parent);
        this.state = st;
        assert (st == TERMINATED || st == INFEASIBLE || st == SUSPENDED);

    }

    public ETLeafNode(int st, ETLeafNode parent) {
        this(SLListOfTerm.EMPTY_LIST, st, parent);
    }

    public String getExceptionName() {
        return exceptionName;
    }

    public SourceElementId getExpression() {
        return expression;
    }

    public void setExceptionName(String exc) {

        if (exc != null) {
            this.expression = ((ITNode) this.getITNodes().getFirst())
                    .getLastExpressionId().getExprId();
        }
        exceptionName = exc;
    }

    public SourceElementId getProgramCounter() {
        return programCounter;
    }

    public void setProgramCounter(SourceElementId pc) {
        programCounter = pc;
    }

    public int getState() {
        return state;
    }

    public ETNode copy(ETNode p) {
        ETLeafNode copy = new ETLeafNode(getBC(), state, (LinkedList) this
                .getITNodes().clone(), p);
        copy.setChildren((LinkedList) this.getChildrenList().clone());
        copy.setExceptionName(this.exceptionName);
        return copy;
    }
}
