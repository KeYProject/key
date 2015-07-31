/**
 * 
 */
package de.uka.ilkd.key.util.joinrule;

import java.util.HashMap;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils.Option;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils.Option.None;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils.Option.Some;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class ProgramVariablesMatchVisitor extends SimultaneousJavaASTVisitor {

    private HashMap<ProgramVariable, ProgramVariable> matches = new HashMap<ProgramVariable, ProgramVariable>();

    /**
     * TODO: Document.
     *
     * @param e1
     * @param e2
     * @param services
     */
    public ProgramVariablesMatchVisitor(ProgramElement e1, ProgramElement e2,
            Services services) {
        super(e1, e2, services);
    }

    /**
     * @return The matched program variables. Is a Option.Some iff
     *         isIncompatible evaluates to false.
     */
    public Option<HashMap<ProgramVariable, ProgramVariable>> getMatches() {
        if (isIncompatible()) {
            return new None<HashMap<ProgramVariable, ProgramVariable>>();
        }
        else {
            return new Some<HashMap<ProgramVariable, ProgramVariable>>(matches);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.util.joinrule.SimultaneousJavaASTVisitor#doDefaultAction
     * (de.uka.ilkd.key.java.SourceElement, de.uka.ilkd.key.java.SourceElement)
     */
    @Override
    protected void doDefaultAction(SourceElement node1, SourceElement node2) {
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.util.joinrule.SimultaneousJavaASTVisitor#visit(de.uka
     * .ilkd.key.logic.op.ProgramVariable,
     * de.uka.ilkd.key.logic.op.ProgramVariable)
     */
    @Override
    public void visit(ProgramVariable x1, ProgramVariable x2) {
        super.visit(x1, x2);

        if (matches.containsKey(x1) && !matches.get(x1).equals(x2)) {
            setIncompatible();
        }
        else {
            matches.put(x1, x2);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.util.joinrule.SimultaneousJavaASTVisitor#visit(de.uka
     * .ilkd.key.logic.op.ProgramVariable,
     * de.uka.ilkd.key.logic.op.ProgramVariable)
     */
    @Override
    public void visit(LocationVariable x1, LocationVariable x2) {
        visit((ProgramVariable) x1, (ProgramVariable) x2);
    }

}
