package de.uka.ilkd.key.rule.match.vm;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher.TermNavigator;

public class BindVariables implements IMatchInstruction {

    private final ImmutableArray<QuantifiableVariable> boundVars;

    public BindVariables(ImmutableArray<QuantifiableVariable> boundVars) {
        this.boundVars = boundVars;
    }

    @Override
    public MatchConditions match(TermNavigator termPosition,
            MatchConditions matchConditions, Services services) {

        ImmutableArray<QuantifiableVariable> variablesToMatchAndBind = 
                termPosition.getCurrentSubterm().boundVars();

        matchConditions = matchConditions.extendRenameTable();
        
        if (variablesToMatchAndBind.size() == boundVars.size()) {
            for (int i = 0; i < boundVars.size() && matchConditions != null; i++) {      
                final QuantifiableVariable templateQVar = boundVars.get(i);
                final QuantifiableVariable qVar = variablesToMatchAndBind.get(i);
                if (templateQVar instanceof LogicVariable) {
                    final RenameTable rt = matchConditions.renameTable();                   
                    if (!rt.containsLocally(templateQVar) && !rt.containsLocally(qVar)) {                           
                        matchConditions = matchConditions.addRenaming(templateQVar, qVar);
                    }
                }
                matchConditions = templateQVar.match(qVar, matchConditions, services);               
            }
        } else {
            matchConditions = null;
        }

        return matchConditions;        
    }

}
