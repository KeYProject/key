package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class LastPrefixElemNotALabelCondition extends VariableConditionAdapter {

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.VariableConditionAdapter#check(de.uka.ilkd.key.logic.op.SchemaVariable, de.uka.ilkd.key.logic.op.SVSubstitute, de.uka.ilkd.key.rule.inst.SVInstantiations, de.uka.ilkd.key.java.Services)
     */
    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services) {
        PosInProgram pos = instMap.getContextInstantiation().prefix();
        
        if (pos.depth() > 0) {
            pos = pos.up();
            ProgramElement program = instMap.getContextInstantiation().contextProgram();
            
            return !(pos.getProgram(program) instanceof LabeledStatement);
        }
        return true;
    }

}
