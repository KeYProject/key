package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;

public class SMTFunctionDef extends SMTFunction {
	
	private SMTTerm sub;
	private List<SMTTermVariable> vars;

	
	
	public SMTFunctionDef(String id, List<SMTTermVariable> vars, SMTSort image, SMTTerm sub){
		
		List<SMTSort> domain = new LinkedList<SMTSort>();
		for(SMTTermVariable v : vars){
			domain.add(v.getSort());
		}
		
		this.id = Util.processName(id);
		this.domainSorts = domain;
		this.imageSort = image;
		this.vars = vars;
		this.sub = sub;		
	}
	
	public SMTFunctionDef(String id, SMTTermVariable var, SMTSort image, SMTTerm sub){
		List<SMTSort> domain = new LinkedList<SMTSort>();
		domain.add(var.getSort());		
		this.id = Util.processName(id);
		this.domainSorts = domain;
		this.imageSort = image;
		this.vars = new LinkedList<SMTTermVariable>();
		vars.add(var);
		this.sub = sub;
	}
	
	public SMTFunctionDef(SMTFunction f, List<SMTTermVariable> vars, SMTTerm sub){
		this.id = f.getId();
		this.domainSorts = f.getDomainSorts();
		this.imageSort = f.getImageSort();
		this.vars = vars;
		this.sub = sub;
	}
	
	public SMTFunctionDef(SMTFunction f, SMTTermVariable var, SMTTerm sub){
		this.id = f.getId();
		this.domainSorts = f.getDomainSorts();
		this.imageSort = f.getImageSort();
		this.vars = new LinkedList<SMTTermVariable>();
		vars.add(var);
		this.sub = sub;
	}



	public SMTTerm getSub() {
		return sub;
	}



	public List<SMTTermVariable> getVars() {
		return vars;
	}
	
	@Override
	public String toString(){
		
		StringBuffer buff = new StringBuffer();
				
		buff.append("(define-fun ");
		buff.append(id);
		buff.append(" (");
		
		for(SMTTermVariable v : vars){
			String varDecl = "( "+ v.getId() + " "+ v.getSort().getId()+" )";
			buff.append(varDecl);			
		}
		
		buff.append(" )");
		buff.append(" ");
		buff.append(imageSort.getId());
		buff.append("\n");
		buff.append(sub.toString(3));
		
		buff.append("\n)");
		
		
		return buff.toString();
		
	}
	
	
	
	
	
	
	
	
	
	

}
