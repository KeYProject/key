package org.key_project.proofmanagement.check.dependency;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.io.intermediate.AppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.AppNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BuiltInAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.TacletAppIntermediate;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.Pair;

public class ContractApplicationCollector extends NodeIntermediateWalker {

    private Set<Pair<String, Modality>> result = new HashSet<>();
    private SpecificationRepository specRepo;

    public ContractApplicationCollector(NodeIntermediate root, SpecificationRepository specRepo) {
        super(root);
        this.specRepo = specRepo;
    }

    public Set<Pair<String, Modality>> getResult() {
        return result;
    }

    @Override
    protected void doAction(NodeIntermediate node) {
        // check if node is UseContractRule
        if (node instanceof AppNodeIntermediate) {
            AppNodeIntermediate appNode = (AppNodeIntermediate) node;
            AppIntermediate appIntermediate = appNode.getIntermediateRuleApp();
            String appName = appIntermediate.getRuleName();

            // relevant rules are:
            //    Use Operation Contract
            //    Use Dependency Contract
            //    Contract_axiom_for_...              (model methods)

            if (appName.equals("Use Operation Contract") || appName.equals("Use Dependency Contract")) {
                BuiltInAppIntermediate biApp = (BuiltInAppIntermediate) appIntermediate;

                // The string may still contain multiple contracts, syntax: contract1#contract2#...
                // split and add all
                // TODO: better use specRepo.splitContract()
                String combinedContracts = biApp.getContract();
                String[] contracts = combinedContracts.split("#");

                // load information about the modality under which the contract was applied
                Modality modality = Modality.getModality(biApp.getModality());
                if (modality == null) {
                    // in default case (e.g. legacy proofs without saved modality information)
                    // we assume diamond modality but print a warning
                    // TODO: really? or is it just incomplete?
                    System.err.println("No saved modality information was found! Assuming \"diamond\"" +
                            " (be careful, this may be unsound)!");
                    modality = Modality.DIA;
                }

                for (String contract : contracts) {
                    result.add(new Pair<>(contract, modality));
                }
            } else if (appName.contains("Contract_axiom_for_")) {
                TacletAppIntermediate tacletApp = (TacletAppIntermediate) appIntermediate;
                String name = tacletApp.getRuleName();
                int methodStart = 19;       // prefix is Contract_axiom_for_
                int methodEnd = name.indexOf("_in_");
                String methodName = name.substring(methodStart, methodEnd);
                int classStart = methodEnd + 4;
                String className = name.substring(classStart);
                // todo: use specRepo to get correct contract name
            }
        }

        /* At the moment, we check only for illegal cycles. If at a later time we want
         * to identify unproven dependencies, we should consider the following rules:
         *      Evaluate Query
         *      Definition_axiom_for_...            model methods
         *      Class_invariant_axiom_...           invariants
         *      Partial_invariant_axiom_...         invariants
         *      todo: user defined taclets?
         *      todo: inlining rules?
         */
    }
}
