package de.uka.ilkd.key.rule.match.vm.instructions;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

/**
 * This instructions matches the variable below a binder (e.g. a quantifier). 
 */
public class BindVariablesInstruction implements MatchInstruction {

    private final VariableBinderSubinstruction[] boundVarBinders;

    public BindVariablesInstruction(ImmutableArray<QuantifiableVariable> boundVars) {
        boundVarBinders = new VariableBinderSubinstruction[boundVars.size()];
        int i = 0;
        for (QuantifiableVariable boundVar : boundVars) {            
            if (boundVar instanceof LogicVariable) {
                boundVarBinders[i] = new LogicVariableBinder((LogicVariable) boundVar);
            } else {
                boundVarBinders[i] = new VariableSVBinder((VariableSV) boundVar);
            }
            i++;
        }
    }


    private interface VariableBinderSubinstruction {        
        public MatchConditions match(LogicVariable instantiationCandidate, MatchConditions matchCond, Services services);
    }

    private static class LogicVariableBinder implements VariableBinderSubinstruction {
        private final LogicVariable templateVar;

        public LogicVariableBinder(LogicVariable templateVar) {
            this.templateVar = templateVar;
        }

        /** 
         * a match between two logic variables is possible if they have been assigned
         * they are same or have been assigned to the same abstract name and the sorts
         *  are equal.
         */
        public MatchConditions match(LogicVariable instantiationCandidate, MatchConditions matchCond, Services services) {
            final RenameTable rt = matchCond.renameTable();                   
            if (!rt.containsLocally(templateVar) && !rt.containsLocally(instantiationCandidate)) {                           
                matchCond = matchCond.addRenaming(templateVar, instantiationCandidate);
            }

            if (templateVar != instantiationCandidate) {
                if(instantiationCandidate.sort() != templateVar.sort() 
                        || !matchCond.renameTable().sameAbstractName(templateVar, instantiationCandidate)) {
                    matchCond = null;
                }
            }
            return matchCond;
        }        
    }

    private static class VariableSVBinder extends MatchSchemaVariableInstruction<VariableSV> 
                                                          implements VariableBinderSubinstruction {

        public VariableSVBinder(VariableSV templateVar) {
            super(templateVar);
        }

        public MatchConditions match(LogicVariable instantiationCandidate, MatchConditions matchCond, Services services) {
            final Object foundMapping = matchCond.getInstantiations().getInstantiation(op);
            if(foundMapping == null) {
                final Term substTerm = services.getTermBuilder().var(instantiationCandidate);
                matchCond = addInstantiation(substTerm, matchCond, services);
            } else if (((Term)foundMapping).op() != instantiationCandidate) {
                matchCond = null;        
            }
            return matchCond;
        }

        @Override
        public MatchConditions match(TermNavigator termPosition,
                MatchConditions matchConditions, Services services) {
            throw new UnsupportedOperationException();
        }

        @Override
        public MatchConditions match(Term instantiationCandidate,
                MatchConditions matchCond, Services services) {
            throw new UnsupportedOperationException();
        } 

    }

    @Override
    public MatchConditions match(TermNavigator termPosition,
            MatchConditions matchConditions, Services services) {

        ImmutableArray<QuantifiableVariable> variablesToMatchAndBind = 
                termPosition.getCurrentSubterm().boundVars();

        matchConditions = matchConditions.extendRenameTable();

        if (variablesToMatchAndBind.size() == boundVarBinders.length) {
            for (int i = 0; i < boundVarBinders.length && matchConditions != null; i++) {      
                // concrete variables must be logic variables
                final LogicVariable qVar = (LogicVariable) variablesToMatchAndBind.get(i);               
                matchConditions = boundVarBinders[i].match(qVar, matchConditions, services);               
            }
        } else {
            matchConditions = null;
        }

        return matchConditions;        
    }

}
