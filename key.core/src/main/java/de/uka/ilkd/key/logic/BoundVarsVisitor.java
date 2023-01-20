package de.uka.ilkd.key.logic;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * Visitor traversing a term and collecting all variables that occur bound. The visitor implements
 * also a continuation on sequents, traversing all of the formulas occuring in the sequent.
 */
public class BoundVarsVisitor extends DefaultVisitor {

    private ImmutableSet<QuantifiableVariable> bdVars =
        DefaultImmutableSet.<QuantifiableVariable>nil();


    /**
     * creates a Visitor that collects all bound variables for the subterms of the term it is called
     * from.
     */
    public BoundVarsVisitor() {
    }

    /**
     * only called by execPostOrder in Term.
     */
    public void visit(Term visited) {
        for (int i = 0, ar = visited.arity(); i < ar; i++) {
            for (int j = 0,
                    boundVarsSize = visited.varsBoundHere(i).size(); j < boundVarsSize; j++) {
                bdVars = bdVars.add(visited.varsBoundHere(i).get(j));
            }
        }
    }

    /**
     * visits a sequent
     */
    public void visit(Sequent visited) {
        for (SequentFormula cf : visited) {
            visit(cf.formula());
        }
    }

    /**
     * returns all the bound variables that have been stored
     */
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {
        return bdVars;
    }

}
