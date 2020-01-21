package org.key_project.proofmanagement.check.dependency;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.speclang.*;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;

public class DependencyNode {

    private SpecificationRepository specRepo;
    private FunctionalOperationContract contract;
    private Map<DependencyNode, DependencyNode> dependencies;

    // TODO: check if these are all problems that can arise
    // and track details about the respective errors for outputting
    public enum Status {
        UNKNOWN, MISSING_PROOFS, MODALITY_CLASH, ILLEGAL_CYCLES, CORRECT
    }

    private Status status;
    private ImmutableSet<FunctionalOperationContract> modalityClashes              = DefaultImmutableSet.nil();
    private ImmutableSet<ImmutableList<FunctionalOperationContract>> illegalCycles = DefaultImmutableSet.nil();

    public DependencyNode(FunctionalOperationContract contract, Map<DependencyNode, DependencyNode> dependencies, SpecificationRepository specRepo) {
        this.specRepo = specRepo;
        this.contract = contract;
        this.dependencies = dependencies;
        status = Status.UNKNOWN;
    }

    public DependencyNode(FunctionalOperationContract contract, SpecificationRepository specRepo) {
        this(contract, new HashMap<>(), specRepo);
    }

    public void addDependency(DependencyNode dependentNode) {
        dependencies.put(dependentNode, dependentNode);
    }

    public FunctionalOperationContract getContract() {
        return contract;
    }

    public  Map<DependencyNode, DependencyNode> getDependencies() {
        return dependencies;
    }

    public SpecificationRepository getSpecRepo() {
        return specRepo;
    }

    public Status getStatus() {
        return status;
    }

    public ImmutableSet<FunctionalOperationContract> getModalityClashes() {
        return modalityClashes;
    }
    public ImmutableSet<ImmutableList<FunctionalOperationContract>> getIllegalCycles() {
        return illegalCycles;
    }

    // adapted from the classes: UseOperationContractRule and ProofCorrectnessMgt
    public boolean isLegal() {
        // are proofs of method contracts missing that are used in the current proof?
        for (DependencyNode currentNode : dependencies.keySet()) {
            if (currentNode == null) {
                status = Status.MISSING_PROOFS;
                return false;
            }
        }
        // is the current method contract concerned with termination?
        if (contract.getModality() == Modality.DIA) {
            // are there some modalities that do not match?
            // this check should be unnecessary
            for (DependencyNode currentNode : dependencies.keySet()) {
                if(currentNode.contract.getModality() == Modality.BOX) {
                    status = Status.MODALITY_CLASH;
                    return false;
                }
            }
            // do the proofs form an illegal cycle?
            for (DependencyNode currentNode : dependencies.keySet()) {
                // TODO: implement ProofCorrectnessMgt.isContractApplicable() here
                if (!isApplicable(currentNode)) {
                    status = Status.ILLEGAL_CYCLES;
                    return false;
                }
            }
        }
        status = Status.CORRECT;
        return true;
    }

    private boolean isApplicable(DependencyNode node) {
        // get initial contracts
        ImmutableSet<Contract> contractsToBeApplied = specRepo.splitContract(node.contract);
        assert contractsToBeApplied != null;
        contractsToBeApplied = specRepo.getInheritedContracts(contractsToBeApplied);
        assert contractsToBeApplied.size() == 1;
        // construct initial paths from initial contracts
        ImmutableSet<ImmutableList<DependencyNode>> paths = DefaultImmutableSet.nil();
        //for (Contract c : contractsToBeApplied) {
        paths = paths.add(ImmutableSLList.<DependencyNode>nil().prepend(node));
        //}
        // check for cycles
        while (!paths.isEmpty()) {
            final Iterator<ImmutableList<DependencyNode>> it = paths.iterator();
            paths = DefaultImmutableSet.<ImmutableList<DependencyNode>>nil();
            while (it.hasNext()) {
                final ImmutableList<DependencyNode> path = it.next();
                final DependencyNode end = path.head();
                if (end.equals(this)) {
                    if (!allHaveMeasuredBy(path.prepend(this))) {
                        return false;
                    }
                } else {
                    // This needs to be edited if we want to allow multiple proofs for the same contract
                    //   i.e. grapped in a loop over all proofs
                    Map<DependencyNode, DependencyNode> currentDependencies = end.dependencies;
                    for (DependencyNode currentDependency : currentDependencies.keySet()) {
                        if (!path.contains(currentDependency)) {
                            final ImmutableList<DependencyNode> extendedPath = path.prepend(currentDependency);
                            paths = paths.add(extendedPath);
                        }
                    }
                }
            }
        }
        return true;
    }
    private boolean allHaveMeasuredBy(ImmutableList<DependencyNode> dependencyNodes) {
        for(DependencyNode currentNode : dependencyNodes) {
            if(!currentNode.contract.hasMby()) {
                return false;
            }
        }
        return true;
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
