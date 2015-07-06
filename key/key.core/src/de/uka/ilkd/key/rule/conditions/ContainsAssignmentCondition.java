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
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class ContainsAssignmentCondition extends de.uka.ilkd.key.rule.VariableConditionAdapter {

    
    private final SchemaVariable expression;
    private final boolean negated;
    

    public ContainsAssignmentCondition(SchemaVariable x, boolean negated) {
        if (!(x instanceof ProgramSV)) {
            throw new IllegalArgumentException("SV for ExpressionContainsNoAssignment must be a program sv");
        }
            
        this.expression = x;
        this.negated = negated;
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.VariableConditionAdapter#check(de.uka.ilkd.key.logic.op.SchemaVariable, de.uka.ilkd.key.logic.op.SVSubstitute, de.uka.ilkd.key.rule.inst.SVInstantiations, de.uka.ilkd.key.java.Services)
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
