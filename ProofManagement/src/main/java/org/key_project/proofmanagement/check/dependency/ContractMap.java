package org.key_project.proofmanagement.check.dependency;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class ContractMap {

    private Map<String, Contract> string2Contract;
    private final SpecificationRepository specRepo;

    public ContractMap(SpecificationRepository specRepo,
                       Map<String, Contract> contractMap) {
        this.specRepo = specRepo;
        string2Contract = contractMap;
    }
    public ContractMap(SpecificationRepository specRepo) {
        this(specRepo, new HashMap<>());
    }

    public Contract lookup(String contractName) {
        if(!string2Contract.containsKey(contractName)) {
            // TODO: find and parse file with respective contract
            Contract contract = specRepo.getContractByName(contractName);

            string2Contract.put(contractName, contract);
        }
        return string2Contract.get(contractName);
    }

}
