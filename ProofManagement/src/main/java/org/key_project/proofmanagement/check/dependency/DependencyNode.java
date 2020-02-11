package org.key_project.proofmanagement.check.dependency;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.speclang.*;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;

public class DependencyNode {

    private SpecificationRepository specRepo;
    private Contract contract;
    private Map<DependencyNode, DependencyNode> dependencies;

    // TODO: check if these are all problems that can arise
    // and track details about the respective errors for outputting
    public enum Status {
        UNKNOWN, MISSING_PROOFS, MODALITY_CLASH, ILLEGAL_CYCLES, CORRECT
    }

    // we keep this (later on we will need it for reporting)
    private Status status;
    private Set<FunctionalOperationContract> modalityClashes = new HashSet<>();
    private Set<ImmutableList<Contract>> illegalCycles = new HashSet<>();

    public DependencyNode(Contract contract, Map<DependencyNode, DependencyNode> dependencies, SpecificationRepository specRepo) {
        this.specRepo = specRepo;
        this.contract = contract;
        this.dependencies = dependencies;
        status = Status.UNKNOWN;
    }

    public DependencyNode(Contract contract, SpecificationRepository specRepo) {
        this(contract, new HashMap<>(), specRepo);
    }

    public void addDependency(DependencyNode dependentNode) {
        dependencies.put(dependentNode, dependentNode);
    }

    // adapted from the classes: UseOperationContractRule/UseDependencyContractRule and ProofCorrectnessMgt
    public boolean isLegal() {
        // are proofs of method contracts missing that are used in the current proof?
        for (DependencyNode currentNode : dependencies.keySet()) {
            if (currentNode == null) {
                status = Status.MISSING_PROOFS;
                return false;
            }
        }

        // TODO: better solution with inheritance
        if (contract instanceof FunctionalOperationContract) {

            FunctionalOperationContract functionalContr = (FunctionalOperationContract)contract;

            // is the current method contract concerned with termination?
            if (functionalContr.getModality() == Modality.DIA) {
                // are there some modalities that do not match?
                // this check should be unnecessary
                for (DependencyNode currentNode : dependencies.keySet()) {
                    if (currentNode.contract instanceof FunctionalOperationContract) {
                        FunctionalOperationContract foc = (FunctionalOperationContract)(currentNode.contract);
                        if (foc.getModality() == Modality.BOX) {
                            status = Status.MODALITY_CLASH;
                            return false;
                        }
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
        }
        status = Status.CORRECT;
        return true;
    }

    public boolean isLegal2() {
        // get target contract via specification repository
        if (contract instanceof FunctionalOperationContract) {
            FunctionalOperationContract func = (FunctionalOperationContract)contract;
            Modality modality = func.getModality();
            if (modality == Modality.BOX || modality == Modality.BOX_TRANSACTION) {
                // if target modality is box than each contract application is legal
                // -> return true without cycle check
                status = Status.CORRECT;
                return true;
            } else if (modality == Modality.DIA || modality == Modality.DIA_TRANSACTION) {
                // has any of the dependency nodes a contract with box?
                // (testing direct dependencies is sufficient here, since we test all nodes)
                for (DependencyNode node : dependencies.keySet()) {
                    if (node.contract instanceof FunctionalOperationContract) {
                        FunctionalOperationContract nodeFunc = (FunctionalOperationContract)node;
                        if (nodeFunc.getModality() == Modality.BOX
                                || nodeFunc.getModality() == Modality.BOX_TRANSACTION) {
                            // invalid -> return false
                            status = Status.MODALITY_CLASH;

                            // TODO: Not really useful:
                            //  There may be undetected clashes since we abort after we found one!
                            modalityClashes.add(nodeFunc);
                            return false;
                        }
                    }
                }
            }
        } /* else if (contract instanceof DependencyContractImpl) {
            // nothing extra to do here
            DependencyContractImpl dep = (DependencyContractImpl)contract;
        }*/

        // find cycles containing with current node
        // TODO: Currently we check the same cycle multiple times (from different nodes)
        // for every found cycle:
        //      if all have measured by clause -> legal
        //      else -> illegal

        status = Status.CORRECT;
        return true;
    }

    private boolean isApplicable(DependencyNode node) {
        // get initial contracts
        ImmutableSet<Contract> contractsToBeApplied = specRepo.splitContract(node.contract);
        assert contractsToBeApplied != null;
        contractsToBeApplied = specRepo.getInheritedContracts(contractsToBeApplied);

        // construct initial paths from initial contracts
        ImmutableSet<ImmutableList<DependencyNode>> paths = DefaultImmutableSet.nil();
        for (Contract c : contractsToBeApplied) {
            paths = paths.add(ImmutableSLList.<DependencyNode>nil().prepend(node));
        }
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
