/**
 * 
 */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition can be used to check whether an assignment expression
 * occurs as a subexpression of a schemavariable instantiation,
 *
 * @author Dominic Scheurer
 *
 */
public class ContainsAssignmentCondition extends de.uka.ilkd.key.rule.VariableConditionAdapter {

    /* the schemavariable matched agains an expression */
    private final SchemaVariable expression;
    
    /* indicates whether the variable condition is used in its negated form, i.e., to check for the
     * absence of an assignment expression.
     */
    private final boolean negated;
    

    /** 
     * creates an instance of the variable condition
     * @param x the schemavariable whose instantiation is to be checked
     * @param negated true iff the check should ensure the absence of an assignment statement
     * @throws an {@link IllegalArgumentException} if the given schemavariable is not a {@link ProgramSV}
     */
    public ContainsAssignmentCondition(SchemaVariable x, boolean negated) {
        if (!(x instanceof ProgramSV)) {
            throw new IllegalArgumentException("SV for ExpressionContainsNoAssignment must be a program sv");
        }
            
        this.expression = x;
        this.negated = negated;
    }
    
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services) {
        if (var != expression) { 
            return true;
        }
        
        
        
        final ProgramElement pe;
        if (instCandidate instanceof Term) {
            return true;
        } else {
            pe = (ProgramElement) instCandidate;
        }
        
        final ContainsAssignment visitor = new ContainsAssignment(pe, services);
        visitor.start();
        
        return negated ^ visitor.result(); 
    }

    
    public String toString() {
        return (negated ? "\\not " : "") + "\\containsAssignment( " + expression.name() + " )"; 
    }
    
    
    /**
     * Visitor iterating over an expression and returning true if an assignment statement has been found.
     */
    private static final class ContainsAssignment extends JavaASTVisitor {
        private boolean result = false;


        public ContainsAssignment(ProgramElement root, Services services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if(node instanceof Assignment) {
                result = true;
            }
        }

        public boolean result() {
            return result;
        }
    }
    
}
