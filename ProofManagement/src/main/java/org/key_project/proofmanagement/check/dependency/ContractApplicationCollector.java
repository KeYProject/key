package org.key_project.proofmanagement.check.dependency;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.proof.io.intermediate.AppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.AppNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BuiltInAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediateWalker;

public class ContractApplicationCollector extends NodeIntermediateWalker {

    private Set<String> myResult = new HashSet<>();

    public ContractApplicationCollector(NodeIntermediate root) {
        super(root);
    }

    public Set<String> getResult() {
        return myResult;
    }

    @Override
    protected void doAction(NodeIntermediate node) {
        // check if node is UseContractRule
        if (node instanceof AppNodeIntermediate) {
            AppNodeIntermediate appNode = (AppNodeIntermediate) node;
            AppIntermediate appIntermediate = appNode.getIntermediateRuleApp();
            String appName = appIntermediate.getRuleName();

            // TODO: do we have to check other contract uses here (e.g. Dependency Contracts, Block Contracts)?
            // TODO: same problem with inlining -> identify all relevant rules

            // todo: relevant rules are:
            //  "use operation contract
            //  "use dependency contract"
            //  ("contract_axiom_for_..." should not be relevant!)

            if (appName.equals("Use Operation Contract") || appName.equals("Use Dependency Contract")) {
                BuiltInAppIntermediate biApp = (BuiltInAppIntermediate) appIntermediate;
                String contract = biApp.getContract();
                myResult.add(contract);
            }
        }
    }
}
