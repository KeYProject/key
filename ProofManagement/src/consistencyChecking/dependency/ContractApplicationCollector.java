package consistencyChecking.dependency;

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
        	if(appName.equals("Use Operation Contract")) {
        		BuiltInAppIntermediate biApp = (BuiltInAppIntermediate)appIntermediate;
        		String contract = biApp.getContract();
        		myResult.add(contract);
        	}
            
        }
    }

}
