package org.key_project.proofmanagement.check.dependency;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;

import java.util.HashMap;
import java.util.Map;

public class DependencyNode {

    private SpecificationRepository specRepo;

    private Contract contract;

    /**
     * Stores each contract used in the proof of the contract of this DependencyNode.
     * Each used contract is mapped to the modality under which it was used.
     * If a contract is used under different modalities, (TODO: possible?)
     * only the strongest one (that one with termination, i.e. diamond) is stored.
     * For dependency contracts, modality may be null as it is not relevant.
     */
    private final Map<DependencyNode, Modality> dependencies = new HashMap<>();

    public Contract getContract() {
        return contract;
    }

    public Map<DependencyNode, Modality> getDependencies() {
        return dependencies;
    }

    // used for Tarjan algorithm
    boolean onStack = false;
    int index = -1;
    int lowLink = 0;

    // TODO: check if these are all problems that can arise
    // and track details about the respective errors for outputting
    public enum Status {
        UNKNOWN, MISSING_PROOFS, MODALITY_CLASH, ILLEGAL_CYCLES, CORRECT
    }

    // we keep this (later on we will need it for reporting)
    //private Status status;
    //private Set<FunctionalOperationContract> modalityClashes = new HashSet<>();
    //private Set<List<Contract>> illegalCycles = new HashSet<>();

    public DependencyNode(Contract contract, SpecificationRepository specRepo) {
        this.contract = contract;
        this.specRepo = specRepo;
    }

    public void addDependency(DependencyNode dependentNode, Modality modality) {
        // TODO: does this work for dependency contracts?
        Modality current = dependencies.get(dependentNode);
        if (current != null) {
            // overwrite current modality only if the given wrong is stronger
            if (!current.terminationSensitive()) {
                dependencies.put(dependentNode, modality);
            }
        } else {
            dependencies.put(dependentNode, modality);
        }
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof DependencyNode) {
            DependencyNode node = (DependencyNode) o;
            if (node.contract.equals(contract)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public String toString() {
        String result = "";
        result = result + contract.getName() + " -> (";
        boolean first = true;
        for(DependencyNode currentNode : dependencies.keySet()) {
            if (!first) result = result + " ";
            result = result + currentNode.contract.getName();
            first = false;
        }
        result = result + ")";
        return result;
    }

}
