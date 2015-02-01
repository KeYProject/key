// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;


/**
 * This class completes the instantiation for a functional operation contract
 * applications. The user is queried for the contract to apply. If in forced mode the combined contracts 
 * will be used.
 */
public class FunctionalOperationContractCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        Services services = goal.proof().getServices();

        if (forced) {
            app = app.forceInstantiate(goal);
            if (app.complete()) {
                return app;
            }
        }
        
        Instantiation inst = UseOperationContractRule.computeInstantiation(
                app.posInOccurrence().subTerm(), services);
        
        ImmutableSet<FunctionalOperationContract> contracts = UseOperationContractRule
                .getApplicableContracts(
                        inst, services);
        
        FunctionalOperationContract[] contractsArr = contracts
                .toArray(new FunctionalOperationContract[contracts.size()]);
        
        ContractConfigurator cc = new ContractConfigurator(
                MainWindow.getInstance(), services, contractsArr,
                "Contracts for " + inst.pm.getName(), true);
        
        if (cc.wasSuccessful()) {
            return  ((UseOperationContractRule) app.rule()).createApp(
                    app.posInOccurrence()).setContract(
                            cc.getContract());
        }
        return app;
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }
    
    /**
     * Checks if the app is supported. 
     * This functionality is also used by the Eclipse plug-ins like the KeYIDE.
     */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
       return app.rule() instanceof UseOperationContractRule;
   }
}