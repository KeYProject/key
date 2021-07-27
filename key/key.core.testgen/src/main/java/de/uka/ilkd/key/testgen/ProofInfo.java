package de.uka.ilkd.key.testgen;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Set;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
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
		//System.out.println("Constants: "+getPOConstants());
		//System.out.println("Assignable: "+getAssignable().sort());
		//getCode();
		//System.out.println("DA");
		//		OracleGenerator gen = new OracleGenerator(services, null);
		//		OracleMethod m = gen.generateOracleMethod(getPostCondition());
		//		System.out.println(m);

	}

	public IProgramMethod getMUT(){		
		SpecificationRepository spec = services.getSpecificationRepository();	
		IObserverFunction f = spec.getTargetOfProof(proof);
		if(f instanceof IProgramMethod){
			return (IProgramMethod) f;
		}
		else{
			return null;
		}		
	}

	public KeYJavaType getTypeOfClassUnderTest(){
		if(getMUT()==null){
			return null;
		}		
		return getMUT().getContainerType();
	}

	public KeYJavaType getReturnType(){
		return getMUT().getType();
	}

	public Contract getContract(){
		ContractPO po = services.getSpecificationRepository().getPOForProof(proof);
		return po.getContract();
	}

	public Term getPostCondition2(){
		Contract c = getContract();
		if(c instanceof FunctionalOperationContract){
			FunctionalOperationContract t = (FunctionalOperationContract) c;
			OriginalVariables orig = t.getOrigVars();
			Term post = t.getPost(services.getTypeConverter().getHeapLDT().getHeap(), orig.self, orig.params, orig.result, orig.exception, orig.atPres, services);
			//System.out.println("Alt post: "+getPostCondition2());
			return post;

		}
		//no post <==> true
		return services.getTermBuilder().tt();
	}

	public Term getPostCondition(){
		Term t = getPO();
		Term post = services.getTermBuilder().tt();
		try{
			post = t.sub(1).sub(1).sub(0);
		}catch(Exception e){
			System.err.println("Could not get PostCondition");
		}

		return post;


	}




	public Term getPreConTerm(){
		Contract c = getContract();		
		if(c instanceof FunctionalOperationContract){
			FunctionalOperationContract t = (FunctionalOperationContract) c;
			OriginalVariables orig = t.getOrigVars();
			Term post = t.getPre(services.getTypeConverter().getHeapLDT().getHeap(), orig.self, orig.params, orig.atPres, services);
			return post;
		}
		//no pre <==> false
		return services.getTermBuilder().ff();
	}

	public Term getAssignable(){
		Contract c = getContract();
		return c.getAssignable(services.getTypeConverter().getHeapLDT().getHeap());
	}

	public String getCode() {

		Term f = getPO();
		JavaBlock block = getJavaBlock(f);

		//	getUpdate(f);
		StringWriter sw = new StringWriter();
		sw.write("   "+getUpdate(f)+"\n");
		PrettyPrinter pw = new CustomPrettyPrinter(sw,false);

		try {
			block.program().prettyPrint(pw);
			return sw.getBuffer().toString();
		} catch (IOException e) {	       
			e.printStackTrace();
		}

		return null;	

	}

	public void getProgramVariables(Term t, Set<Term> vars){

//		System.out.println("FindConstants: "+t+ " cls "+t.op().getClass().getName());
//		if(t.op() instanceof LocationVariable && t.subs().size() == 0 && isRelevantConstant(t)){
//			vars.add(t);
//		}

		if(t.op() instanceof ProgramVariable && isRelevantConstant(t)){			
			vars.add(t);
		}

		for(Term sub : t.subs()){
			getProgramVariables(sub, vars);
		}

	}

	private boolean isRelevantConstant(Term c){
		Operator op = c.op();
		
		if(isTrueConstant(op) || isFalseConstant(op)){
			return false;
		}
		
		Sort s = c.sort();
		
		Sort nullSort = services.getJavaInfo().getNullType().getSort();
		Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
		Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
		Sort boolSort = services.getTypeConverter().getBooleanLDT().targetSort();
		
		if(s.equals(nullSort)){
			return false;
		}
		
		if(s.extendsTrans(objSort) || s.equals(intSort) || s.equals(boolSort)){
			return true;
		}
		
		return false;
		
	}
	
	private boolean isTrueConstant(Operator o) {
		return o.equals(services.getTypeConverter().getBooleanLDT().getTrueConst());
	}
	
	private boolean isFalseConstant(Operator o) {
		return o.equals(services.getTypeConverter().getBooleanLDT().getFalseConst());
	}

	public Term getPO() {
		return proof.root().sequent().succedent().get(0).formula();
	}






	public String getUpdate(Term t){
		if(t.op() instanceof UpdateApplication){
			//UpdateApplication u = (UpdateApplication) t.op();
			return processUpdate(UpdateApplication.getUpdate(t));
		}
		else{
			String result = "";
			for(Term s : t.subs()){
				result += getUpdate(s);
			}
			return result;
		}

	}




	private String processUpdate(Term update) {
		if(update.op() instanceof ElementaryUpdate){			
			ElementaryUpdate up = (ElementaryUpdate) update.op();			
			if(up.lhs().sort().extendsTrans(services.getTypeConverter().getHeapLDT().targetSort())){
				return "";
			}			
			return "   \n"+up.lhs().sort()+" "+up.lhs().toString()+" = "+update.sub(0)+";";
		}
		String result = "";
		for(Term sub : update.subs()){
			result += processUpdate(sub);
		}
		return result;
	}

	public JavaBlock getJavaBlock(Term t){		
		if(t.containsJavaBlockRecursive()){
			if(!t.javaBlock().isEmpty()){
				return t.javaBlock();
			}
			else{
				for(Term s : t.subs()){
					if(s.containsJavaBlockRecursive()){
						return getJavaBlock(s);
					}
				}
			}
		}		
		return null;		
	}





}
