// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/** 
 * Created on: Mar 23, 2011
 */
package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;

/**
 * 
 * 
 * @author Aboubakr Achraf El Ghazi
 * 
 */
public class SMTTermQuant extends SMTTerm {

	public enum Quant {
		FORALL, EXISTS;
		
		public Quant sign (boolean pol) {
			switch (this) {
			case FORALL:
				if (pol)
					return this;
				return EXISTS;
			case EXISTS:
				if (pol)
					return this;
				return FORALL;
			default:
				throw new RuntimeException("Unexpected: Quant in neg() : "+this);
			}
		}
	};

	Quant quant;
	List<SMTTermVariable> bindVars;
	SMTTerm sub;
	List<List<SMTTerm>> pats;

	public SMTTermQuant(Quant quant, List<SMTTermVariable> bindVars, SMTTerm sub, List<List<SMTTerm>> pats) {
		this.quant = quant;
		this.bindVars = bindVars;
		this.sub = sub;
		this.pats = pats;
		this.sub.upp = this;
		for (SMTTermVariable var : this.bindVars) {
			var.quant = this;
		}
	}

	public SMTTermQuant(Quant quant, List<SMTTermVariable> bindVars, SMTTerm sub, SMTTerm pat) {
		this.quant = quant;
		this.bindVars = bindVars;
		this.sub = sub;
		this.pats = toList(toList(pat));
		this.sub.upp = this;
		for (SMTTermVariable var : this.bindVars) {
			var.quant = this;
		}
	}

	
	public Quant getQuant() {
		return quant;
	}

	public void setQuant(Quant quant) {
		this.quant = quant;
	}

	public List<SMTTermVariable> getBindVars() {
		return bindVars;
	}

	public void setBindVars(List<SMTTermVariable> bindVars) {
		this.bindVars = bindVars;
	}

	public SMTTerm getSub() {
		return sub;
	}

	public void setSub(SMTTerm sub) {
		this.sub = sub;
	}
	
	/**
	 * @return the pats
	 */
	public List<List<SMTTerm>> getPats() {
		return pats;
	}

	/**
	 * @param pat the pat to set
	 */
	public void setPats(List<List<SMTTerm>> pats) {
		this.pats = pats;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getQuantVars() {
		List<SMTTermVariable> vars = sub.getQuantVars();
		vars.addAll(bindVars);
		return vars;
	}
	
	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getUQVars() {
		List<SMTTermVariable> vars = sub.getUQVars();
		if (quant.equals(Quant.FORALL))
			vars.addAll(bindVars);
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getEQVars() {
		List<SMTTermVariable> vars = sub.getEQVars();
		if (quant.equals(Quant.EXISTS))
			vars.addAll(bindVars);
		return vars;
	}
	

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getVars() {
		return sub.getVars();
	}
	
	/** {@inheritDoc} */
	@Override
	public SMTSort sort () {
		return SMTSort.BOOL;
	}
	
	/** {@inheritDoc} */
	@Override
	public boolean occurs (SMTTermVariable a) {
		//TODO: we should check for variable id value equality: \exists x \in bindVars | x.id.equals(a.id)
		for(SMTTermVariable v : bindVars){
			if(a.getId().equals(v.getId())){
				return true;
			}
		}
		return sub.occurs(a);
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs (String id) {
		//TODO: we should check for variable id value equality: \exists x \in bindVars | x.id.equals(a.id)
		for(SMTTermVariable var : bindVars){
			if(var.getId().equals(id))
				return true;
		}
		return sub.occurs(id);
	}
	
	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTermVariable a, SMTTerm b) {
		//TODO: we should check for variable id value equality: \exists x \in bindVars | x.id.equals(a.id)
		for(SMTTermVariable v : bindVars){
			if(v.equals(a)){
				return this;
			}
		}
//		return new TermQuant(quant, bindVars,sub.substitute(a, b), pats);
		return sub.substitute(a, b).quant(quant, bindVars, pats);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTerm a, SMTTerm b) {
		
		if (this.equals(a))
			return b;
		
		//TODO: we should check for variable id value equality: \exists x \in bindVars | x.id.equals(a.id)
		for(SMTTermVariable v : bindVars){
			if(v.equals(a)){
				return this;
			}
		}
//		return new TermQuant(quant, bindVars,(Term) sub.substitute(a, b), pats);
		return sub.substitute(a, b).quant(quant, bindVars, pats);
	}
	
	/** {@inheritDoc} */
	@Override
	public SMTTerm replace (SMTTermCall a, SMTTerm b) {
		
//		return new TermQuant(quant, bindVars,(Term) sub.replace(a, b), pats);
		return sub.replace(a, b).quant(quant, bindVars, pats);
	}
	
	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate (SMTTermVariable a, SMTTerm b) {
		
		if (!b.isCons())
			throw new RuntimeException("Unexpected: Variable instantiation with a non constante '"+b+"'");

		List<SMTTermVariable> newVars = new LinkedList<SMTTermVariable>();
		for (SMTTermVariable v : bindVars) {
			if (!v.equals(a))
				newVars.add(v);
		}

		if (newVars.isEmpty())
			return sub.instantiate(a, b);

		if (newVars.size() < bindVars.size())
			/**
			 * 1. Some SMT solvers like Z3 requires patterns to contains all binded variables
			 * 2. Some terms of the patterns can contains more that one variable
			 * 3. Instantiation of quantified variables should can destroy the well-sortedness of patterns term. 
			 * Because of 1-3 and for simplicity, we just drop the entry pattern its the quantifier is instantiated. 
			**/
			return sub.instantiate(a, b).quant(quant, newVars);
		return sub.instantiate(a, b).quant(quant, newVars, pats);
		
		
	}
	
	@Override
	public SMTTermQuant copy () {
	    
	    	List<SMTTermVariable> newVariables = new LinkedList<SMTTermVariable>();
	    	for(SMTTermVariable var : bindVars){
	    	    newVariables.add(var.copy());
	    	}	    
	    
		return new SMTTermQuant(this.quant, newVariables, this.sub.copy(), this.pats);
	}
	
	@Override
	public boolean equals (Object term) {
		if (term == null)
			return false;
		
		if (this == term)
			return true;
		
		if (!(term instanceof SMTTermQuant)) 
			return false;
		SMTTermQuant qt = (SMTTermQuant) term;
		
		if (!this.quant.equals(qt.quant))
			return false;
		
		if (this.bindVars.size() != qt.bindVars.size())
			return false;
		
		
		// TODO: Variable ordering do not affect equality
		for (int i = 0; i < this.bindVars.size(); i++) {
//			if (!this.bindVars.get(i).sort.equals(qt.bindVars.get(i).sort))
//				return false;
//			
//			if (!this.bindVars.get(i).id.equals(qt.bindVars.get(i).id))
//				return false;
			
			if (!qt.getBindVars().contains(this.bindVars.get(i)))
				return false;
		}
		
		return this.sub.equals(qt.sub);
	}

//	public boolean equals (Term term) {
//		if (term == null)
//			return false;
//		
//		if (this == term)
//			return true;
//		
//		if (!(term instanceof TermQuant)) 
//			return false;
//		TermQuant qt = (TermQuant) term;
//		
//		if (!this.quant.equals(qt.quant))
//			return false;
//		
//		if (this.bindVars.size() != qt.bindVars.size())
//			return false;
//		
//		for (int i = 0; i < this.bindVars.size(); i++) {
//			if (!this.bindVars.get(i).sort.equals(qt.bindVars.get(i).sort))
//				return false;
//			
//			if (!this.bindVars.get(i).id.equals(qt.bindVars.get(i).id))
//				return false;
//		}
//		
//		return this.sub.equals(qt.sub);
//	}
//
//	public boolean equals (TermQuant qt) {
//		if (qt == null)
//			return false;
//		
//		if (this == qt)
//			return true;
//		
//		if (!this.quant.equals(qt.quant))
//			return false;
//		
//		if (this.bindVars.size() != qt.bindVars.size())
//			return false;
//		
//		for (int i = 0; i < this.bindVars.size(); i++) {
//			if (!this.bindVars.get(i).sort.equals(qt.bindVars.get(i).sort))
//				return false;
//			
//			if (!this.bindVars.get(i).id.equals(qt.bindVars.get(i).id))
//				return false;
//		}
//		
//		return this.sub.equals(qt.sub);
//	}
	
	@Override
	public int hashCode() {
		int ret = quant.hashCode();
		
		for (SMTTermVariable var : bindVars) {
			ret = ret + var.hashCode() * 10;
		}

		return ret + sub.hashCode()*100;
	}
	
	public String toSting (){
		return toString(0);
	}
	public String toString(int nestPos) {
		StringBuffer tab =  new StringBuffer();
		for(int i = 0; i< nestPos; i++) {
			tab = tab.append(" ");
		}

		StringBuffer buff = new StringBuffer();
		buff.append(tab);
		
		if (bindVars.size() == 0) {
			return sub.toString(nestPos);
		}
		
		if (quant == Quant.FORALL) {
			buff.append("(forall ");
			
		} else{
			
			if(quant == Quant.EXISTS) {
				buff.append("(exists ");
				
			} else {
				throw new RuntimeException("Unexpected: quantifier notIn {FORALL, EXISTS}");
			}
			
	
		}
		
		buff.append("(");
		for (SMTTermVariable var : bindVars) {
			buff.append(" ("+var.getId()+" "+var.getSort().getTopLevel().getId()+")");
		}
		buff.append(" )");
		
		if(pats != null)
			if(!pats.isEmpty())
				buff.append(" (! ");

		buff.append("\n");
		
		buff.append(sub.toString(nestPos+1));
		
		buff.append("\n");

//		if (pat != null) {
//			buff.append(tab + " " + ":pattern ( ");
////			buff.append("\n");
////			buff.append(pat.toString(nestPos+1));
//			buff.append(pat.toString(0));
////			buff.append("\n");
////			buff.append(tab + " }");
//			buff.append(" )");
//			buff.append(")");
//		}
		
		if(pats != null){
			if(!pats.isEmpty()){
				
				for (List<SMTTerm> patList : pats) {
					buff.append(tab + " " + " " + ":pattern ( ");
		
					for (SMTTerm pat : patList) {
						buff.append(pat.toString(0));
						buff.append(" ");
					}
		
					buff.append(")");
					buff.append("\n");
				}
				
				buff.append(tab + " " + " )");
			}
				
		}

		
		buff.append("\n");
		buff.append(tab);		
		buff.append(")");
		
		return buff.toString();
	
		
	}

}