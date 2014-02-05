/** 
 * Created on: Mar 17, 2011
 */
package de.uka.ilkd.key.smt.lang;


import java.util.LinkedList;
import java.util.List;


/**
 * SMTLib supports functions as well as predicates. We only use functions and represent predicates as boolean valued functions.
 * As consequence a function application can build a term as well as a formula.
 *
 * @author Aboubakr Achraf El Ghazi
 *
 */
public class SMTTermCall extends SMTTerm{

	SMTFunction func;
		 List<SMTTerm> args;
	//List<? extends SMTTerm> args;

	//public TermCall(SMTFunction func, List<? extends SMTTerm> args){

		


			public SMTTermCall(SMTFunction func, List<SMTTerm> args){
		
		if(func == null){
			throw new RuntimeException("Null fun call!");
		}
		
		this.func = func;
		this.args = args;
		for (SMTTerm arg : this.args) {
			arg.upp = this;
		}
	}

	public SMTTermCall(SMTFunction func, SMTTerm arg){
		
		if(func == null){
			throw new RuntimeException("Null fun call!");
		}
		
		
		this.func = func;

		List<SMTTerm> args = new LinkedList<SMTTerm>();
		args.add(arg);
		arg.upp = this;
		this.args = args;
	}

	public SMTFunction getFunc() {
		return func;
	}

	public void setFunc(SMTFunction func) {
		this.func = func;
	}

//	public List<? extends SMTTerm> getArgs() {
//		return args;
//	}
		public List<SMTTerm> getArgs() {
			return args;
		}

	public void setArgs(List<SMTTerm> args) {
		this.args = args;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getQuantVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		for(int i = 0; i< args.size(); i++){
			vars.addAll(args.get(i).getQuantVars());
		}
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getUQVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		for(int i = 0; i< args.size(); i++){
			vars.addAll(args.get(i).getUQVars());
		}
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getEQVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		for(int i = 0; i< args.size(); i++){
			vars.addAll(args.get(i).getEQVars());
		}
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();

		for(int i = 0; i< args.size(); i++){
			vars.addAll(args.get(i).getVars());
		}
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public SMTSort sort () {
		return func.getImageSort();
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs (SMTTermVariable a) {
		for(SMTTerm arg : args){
			if (arg.occurs(a))
				return true;
		}
		return false;
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs (String id) {
		if (func.getId().equals(id))
			return true;
		for(SMTTerm arg : args){
			if (arg.occurs(id))
				return true;
		}
		return false;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTermVariable a, SMTTerm b) {
		LinkedList<SMTTerm> newArgs = new LinkedList<SMTTerm>();
		for(SMTTerm arg : args){
			newArgs.add(arg.substitute(a, b));
		}
		return new SMTTermCall (func, newArgs);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTerm a, SMTTerm b) {

		if (this.equals(a))
			return b;

		LinkedList<SMTTerm> newArgs = new LinkedList<SMTTerm>();
		for(SMTTerm arg : args){
			newArgs.add(arg.substitute(a, b));
		}
		return new SMTTermCall (func, newArgs);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm replace (SMTTermCall a, SMTTerm b) {

		if (this.equals(a))
			return b;

		LinkedList<SMTTerm> newArgs = new LinkedList<SMTTerm>();
		for(SMTTerm arg : args){
			newArgs.add(arg.replace(a, b));
		}
		return new SMTTermCall (func, newArgs);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate (SMTTermVariable a, SMTTerm b) {
		LinkedList<SMTTerm> newArgs = new LinkedList<SMTTerm>();
		for(SMTTerm arg : args){
			newArgs.add(arg.instantiate(a, b));
		}
		//		return new TermCall (func, newArgs);
		return SMTTerm.call(func, newArgs);
	}

	@Override
	public SMTTermCall copy () {

		SMTFunction f = new SMTFunction(func.getId(),func.getDomainSorts(),func.getImageSort());

		List<SMTTerm> newArgs = new LinkedList<SMTTerm>();
		for(SMTTerm t : args){
			newArgs.add(t.copy());
		}


		return new SMTTermCall(f, newArgs);
	}

	@Override
	public boolean equals (Object term) {

		if (this == term)
			return true;

		if (term == null)
			return false;

		if (!(term instanceof SMTTermCall)) 
			return false;
		SMTTermCall tc = (SMTTermCall) term;

		if (!this.func.equals(tc.func))
			return false;

		if (this.args.size() != tc.args.size())
			return false;

		for (int i = 0; i < this.args.size(); i++) {
			if (!this.args.get(i).equals(tc.args.get(i)))
				return false;
		}

		return true;
	}

	//	public boolean equals (Term term) {
	//		if (term == null)
	//			return false;
	//	
	//		if (this == term)
	//			return true;
	//		
	//		if (!(term instanceof TermCall)) 
	//			return false;
	//		TermCall tc = (TermCall) term;
	//		
	//		if (!this.func.equals(tc.func))
	//			return false;
	//		
	//		if (this.args.size() != tc.args.size())
	//			return false;
	//		
	//		for (int i = 0; i < this.args.size(); i++) {
	//			if (!this.args.get(i).equals(tc.args.get(i)))
	//				return false;
	//		}
	//		
	//		return true;
	//	}
	//
	//	public boolean equals (TermCall tc) {
	//		if (tc == null)
	//			return false;
	//			
	//		if (this == tc)
	//			return true;
	//		
	//		if (!this.func.equals(tc.func))
	//			return false;
	//		
	//		if (this.args.size() != tc.args.size())
	//			return false;
	//		
	//		for (int i = 0; i < this.args.size(); i++) {
	//			if (!this.args.get(i).equals(tc.args.get(i)))
	//				return false;
	//		}
	//		
	//		return true;
	//	}

	@Override
	public int hashCode() {
		int ret = func.getId().hashCode();
		int base = 10;
		int i = 1;

		for (SMTTerm arg : args) {
			ret = ret + arg.hashCode() * (base^i);
			i++;
		}

		return ret;
	}

	public String toSting (){
		return toString(0);
	}
	@Override
	public String toString (int nestPos) {

		StringBuffer tab =  new StringBuffer();
		for(int i = 0; i < nestPos; i++) {
			tab = tab.append(" ");
		}

		if (args.isEmpty())
			return tab + func.getId();

		StringBuffer buff = new StringBuffer();
		buff.append(tab);

		buff.append("("+func.getId());

		for (SMTTerm arg : args) {
			buff.append(" " + arg.toString(0));
		}
		buff.append(")");

		return buff.toString();
	}


}
