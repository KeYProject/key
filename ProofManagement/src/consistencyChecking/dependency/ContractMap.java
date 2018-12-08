package consistencyChecking.dependency;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class ContractMap {
	
	private Map<String, FunctionalOperationContract> myContractMap = new HashMap<>();
	
	public FunctionalOperationContract lookup(String contractName) {
		if(!myContractMap.containsKey(contractName)) {
			// TODO: find and parse file with respective contract
		}
		return myContractMap.get(contractName);
	}

}
