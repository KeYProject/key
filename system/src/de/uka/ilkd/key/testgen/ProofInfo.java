package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class ProofInfo {

	private Proof proof;	

	private Services services;

	public ProofInfo(Proof proof) {
		this.proof = proof;
		this.services = proof.getServices();
	}

	public IProgramMethod getMUT(){		
		SpecificationRepository spec = services.getSpecificationRepository();	
		IObserverFunction f = spec.getTargetOfProof(proof);
		IProgramMethod m = (IProgramMethod) f;
		return m;
		
	}

	public KeYJavaType getTypeOfClassUnderTest(){
		return getMUT().getContainerType();
	}

	public KeYJavaType getReturnType(){
		return getMUT().getType();
	}

	public Contract getContract(){
		ContractPO po = services.getSpecificationRepository().getPOForProof(proof);
		return po.getContract();
	}

	public Term getPostCondition(){
		Contract c = getContract();
		if(c instanceof FunctionalOperationContract){
			FunctionalOperationContract t = (FunctionalOperationContract) c;
			OriginalVariables orig = t.getOrigVars();
			Term post = t.getPost(services.getTypeConverter().getHeapLDT().getHeap(), orig.self, orig.params, orig.result, orig.exception, orig.atPres, services);
			return post;
		}
		//no post <==> true
		return services.getTermBuilder().tt();
	}

	public Term getPreConTerm(){
		Contract c = getContract();
		if(c instanceof FunctionalOperationContract){
			FunctionalOperationContract t = (FunctionalOperationContract) c;
			OriginalVariables orig = t.getOrigVars();
			Term post = t.getPre(services.getTypeConverter().getHeapLDT().getHeap(), orig.self, orig.params, orig.atPres, services);
			return post;
		}
		//no post <==> true
		return services.getTermBuilder().tt();
	}
	
	public Term getAssignable(){
		Contract c = getContract();
		return c.getAssignable(services.getTypeConverter().getHeapLDT().getHeap());
	}



}
