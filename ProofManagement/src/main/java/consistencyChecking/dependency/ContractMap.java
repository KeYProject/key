package consistencyChecking.dependency;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class ContractMap {
	
	private Map<String, FunctionalOperationContract> myContractMap;
	private final SpecificationRepository specRepo;
	
	public ContractMap(SpecificationRepository specRepo,
	                   Map<String, FunctionalOperationContract> contractMap) {
	    this.specRepo = specRepo;
		myContractMap = contractMap;
	}
	public ContractMap(SpecificationRepository specRepo) {
		this(specRepo, new HashMap<>());
	}
	
	public FunctionalOperationContract lookup(String contractName) {
		if(!myContractMap.containsKey(contractName)) {
			// TODO: find and parse file with respective contract
		    Contract contract = specRepo.getContractByName(contractName);

		    assert contract instanceof FunctionalOperationContract;

		    myContractMap.put(contractName, (FunctionalOperationContract) contract);
		}
		return myContractMap.get(contractName);
	}

}
