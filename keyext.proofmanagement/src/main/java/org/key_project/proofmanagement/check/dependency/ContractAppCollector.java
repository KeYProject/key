/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check.dependency;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.intermediate.AppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.AppNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BuiltInAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.TacletAppIntermediate;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.ContractAxiom;

import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.Logger;
import org.key_project.util.collection.ImmutableSet;

import static org.key_project.proofmanagement.check.dependency.DependencyGraph.EdgeType.TERMINATION_INSENSITIVE;
import static org.key_project.proofmanagement.check.dependency.DependencyGraph.EdgeType.TERMINATION_SENSITIVE;

/*
 * TODO: At the moment, we check only for illegal cycles. If at a later time we want
 * to identify unproven dependencies, we should consider the following rules:
 * Class_invariant_axiom_... invariants
 * Partial_invariant_axiom_... invariants
 * user defined taclets
 */
/**
 * Walker for collecting contract applications. This includes:
 * <ul>
 * <li>operation contracts (applied inside box or diamond modalities)</li>
 * <li>dependency contracts</li>
 * <li>model method contract axioms</li>
 * </ul>
 *
 * @author Wolfram Pfeifer
 */
public class ContractAppCollector extends NodeIntermediateWalker {
    /**
     * the proof we search for contract applications (needed to get the SpecificationRepository,
     * JavaInfo, ...)
     */
    private Proof proof;

    /** the logger to print out messages */
    private Logger logger;

    /** the contracts (by name) as found by this collector as well as the termination type */
    private Map<String, DependencyGraph.EdgeType> result = new HashMap<>();

    /**
     * Creates a new collector for the given proof, starting at given root node.
     *
     * @param root the root node to start from
     * @param proof the proof object (needed to get SpecificationRepository, JavaInfo, ...)
     * @param logger the logger to print out messages
     */
    public ContractAppCollector(NodeIntermediate root, Proof proof, Logger logger) {
        super(root);
        this.proof = proof;
        this.logger = logger;
    }

    public Map<String, DependencyGraph.EdgeType> getResult() {
        return result;
    }

    @Override
    protected void doAction(NodeIntermediate node) {
        if (node instanceof AppNodeIntermediate) {
            AppNodeIntermediate appNode = (AppNodeIntermediate) node;
            AppIntermediate appIntermediate = appNode.getIntermediateRuleApp();
            String ruleName = appIntermediate.getRuleName();

            // relevant rules are:
            // Use Operation Contract builtin-rule
            // Use Dependency Contract builtin-rule
            // Contract_axiom_for_... taclet (model methods)
            if (ruleName.equals("Use Operation Contract")
                    || ruleName.equals("Use Dependency Contract")) {
                BuiltInAppIntermediate biApp = (BuiltInAppIntermediate) appIntermediate;
                extractContractsFromBuiltin(biApp);
            } else if (ruleName.contains("Contract_axiom_for_")) {
                TacletAppIntermediate tacletApp = (TacletAppIntermediate) appIntermediate;
                extractContractFromContractTaclet(tacletApp);
            }
        }
    }

    /**
     * Extracts the contract from the given Taclet node.
     *
     * @param tacletApp the Taclet node to extract the contract from
     */
    private void extractContractFromContractTaclet(TacletAppIntermediate tacletApp) {
        /*
         * With the current implementation in KeY, the name of the rule is always
         * Contract_axiom_for_m_in_C
         * where m stands for the method name and C for the class name.
         * TODO: for (seldom used) class names with underscores, this may fail.
         * We could use a regex to be safe here.
         */

        // extract class name and method name from Taclet name
        String name = tacletApp.getRuleName();
        int methodEnd = name.indexOf("_in_");
        int classStart = methodEnd + 4;
        String className = name.substring(classStart);

        // get type of class from JavaInfo
        Services services = proof.getInitConfig().getServices();
        KeYJavaType classType = services.getJavaInfo().getKeYJavaType(className);

        if (classType == null) {
            // since className does not include package prefix, we have to search the complete list
            Set<KeYJavaType> allTypes = services.getJavaInfo().getAllKeYJavaTypes();
            for (KeYJavaType t : allTypes) {
                if (t.getJavaType().getName().equals(className)) {
                    // found match
                    classType = t;
                    break;
                }
            }

            if (classType == null) {
                // still no hit -> critical error
                throw new NullPointerException("KeYJavaType still is null for class with name "
                    + className);
            }
        }

        // get all class axioms of the class via SpecificationRepository, filter for name
        SpecificationRepository specRepo = proof.getServices().getSpecificationRepository();
        String axiomName = tacletApp.getRuleName().replace('_', ' ');
        Set<ClassAxiom> axioms = specRepo.getClassAxioms(classType).toSet();
        List<ClassAxiom> axiomList = axioms.stream()
                .filter(a -> a.getName().equals(axiomName))
                .collect(Collectors.toList());
        /*
         * the assertions below always hold for current KeY implementation, where
         * only one model method with same name is allowed (no overloading)
         */
        assert axiomList.size() == 1;
        ClassAxiom axiom = axiomList.get(0);

        // found axiom always is a contract axiom, target always a program (model) method!
        assert axiom instanceof ContractAxiom;
        ContractAxiom contractAxiom = (ContractAxiom) axiom;
        IObserverFunction obs = contractAxiom.getTarget();
        assert obs instanceof ProgramMethod;
        ProgramMethod modelMethod = (ProgramMethod) obs;
        assert modelMethod.getMethodDeclaration().isModel();

        // find the searched contract with specRepo, class type, and program method
        Set<Contract> contractsSet = specRepo.getContracts(classType, modelMethod).toSet();
        List<Contract> contractList = new ArrayList<>(contractsSet);

        // TODO: this is not the case if multiple contracts are combined with also keyword,
        // however, in this case the contract axioms are completely broken anyway
        assert contractList.size() == 1;
        Contract contract = contractList.get(0);

        // model method contract application is always termination sensitive!
        result.putIfAbsent(contract.getName(), TERMINATION_SENSITIVE);
    }

    /**
     * Extracts the contracts from a builtin rule. Note that these may be multiple contracts,
     * since KeY sometimes combines contracts!
     *
     * @param biApp the builtin rule node to extract the contracts from
     */
    private void extractContractsFromBuiltin(BuiltInAppIntermediate biApp) {
        // The string may still contain multiple contracts, syntax: contract1#contract2#...
        // split and add all
        SpecificationRepository specRepo = proof.getServices().getSpecificationRepository();
        Contract c = specRepo.getContractByName(biApp.getContract());
        ImmutableSet<Contract> contracts = specRepo.splitContract(c);

        // load information about the modality under which the contract was applied
        Modality modality = Modality.getModality(biApp.getModality());
        DependencyGraph.EdgeType edgeType;
        if (modality == null) {
            // in default case (e.g. legacy proofs without saved modality information)
            // we assume diamond modality but print a warning
            logger.print(LogLevel.WARNING, "No saved modality information was found!" +
                " Assuming \"diamond\" (incomplete for box contracts)!");
            edgeType = TERMINATION_SENSITIVE;
        } else if (modality.terminationSensitive()) {
            edgeType = TERMINATION_SENSITIVE;
        } else {
            edgeType = TERMINATION_INSENSITIVE;
        }

        for (Contract contract : contracts) {
            // if an application of this contract has already been found, we update only if the
            // more recently found termination type is stronger
            DependencyGraph.EdgeType current = result.get(contract.getName());
            if (current == null || current == TERMINATION_INSENSITIVE) {
                result.put(contract.getName(), edgeType);
            }
        }
    }
}
