/** 
 * Created on: Mar 16, 2011
 */
package de.uka.ilkd.key.smt.lang;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 *
 *
 * @author Aboubakr Achraf El Ghazi
 *
 */
public class SMTFile {
	
	List<SMTSort> sorts;
	List<SMTFunction> functions;
	List<SMTTerm> formulas;
	String scope;
	String defaultLogic;
	
	
	public SMTFile () {
		sorts = new LinkedList<SMTSort>();
		functions = new LinkedList<SMTFunction>();
		formulas = new LinkedList<SMTTerm>();
	}	
	public List<SMTSort> getSorts() {
		return sorts;
	}

	public void setSorts(List<SMTSort> sorts) {
		this.sorts = sorts;
	}

	public List<SMTFunction> getFunctions() {
		return functions;
	}

	public void setFunctions(List<SMTFunction> functions) {
		this.functions = functions;
	}

	public List<SMTTerm> getFormulas() {
		return formulas;
	}

	public void setFormulas(List<SMTTerm> formulas) {
		this.formulas = formulas;
	}
	

	public void addSort (SMTSort sort) {
		if (!sorts.contains(sort));
			sorts.add(sort);
	}
	
	public void addFunction (SMTFunction function) {
		functions.add(function);
	}

	public void removeFunction (SMTFunction function) {
		functions.remove(function);
	}

	public void removeAllFunction (Set<SMTFunction> functions) {
		functions.removeAll(functions);
	}

	public void addFormula (SMTTerm formula) {
		formulas.add(formula);
	}
	
	public void addFormulas (List<SMTTerm> terms) {
		formulas.addAll(terms);
	}
	
	/**
	 * @return the defaultLogic
	 */
	public String getDefaultLogic() {
		return defaultLogic;
	}
	/**
	 * @param defaultLogic the defaultLogic to set
	 */
	public void setDefaultLogic(String defaultLogic) {
		this.defaultLogic = defaultLogic;
	}
	
	/**
	 * @return the scope
	 */
	public String getScope() {
		return scope;
	}
	/**
	 * @param scope the scope to set
	 */
	public void setScope(String scope) {
		this.scope = scope;
	}
	
	
	public String toString(){
		
		StringBuffer out = new StringBuffer();
		
		
		out.append(";==========OPTIONS==========\n\n");
		
		out.append("(set-option :print-success true) \n");
		out.append("(set-option :produce-unsat-cores true)\n");
		out.append("(set-option :produce-models true)\n");
		//out.append("(set-option :produce-proofs true)\n");
		
		out.append("\n;==========SORTS==========\n");
		
		for(SMTSort s: sorts){
			out.append('\n');
			out.append(s.toString());
			out.append('\n');
			
		}
		
		out.append("\n;==========FUNCTIONS==========\n");
		
		for(SMTFunction f : functions){
			out.append('\n');
			if(f.getComment()!=null){
				String comment = f.getComment();
				comment = ";"+comment.replace('\n', ' ');				
				out.append(comment);
				out.append('\n');
			}
			out.append(f.toString());
			out.append('\n');
			
		}
		
		out.append("\n;==========ASSERTIONS==========\n");
		
		for(SMTTerm f : formulas){
			
			if(f== SMTTerm.TRUE) continue;
			out.append('\n');
			if(f.getComment()!=null){
				String comment = f.getComment();
				comment = ";"+comment.replace('\n', ' ');				
				out.append(comment);
				out.append('\n');
			}
			
			out.append("(assert ");
			out.append(f.toString());
			out.append(")");
			out.append('\n');
			
		}
		
		out.append("(check-sat)\n");
		//out.append("(get-model)");
		
		
		return out.toString();
		
		
		
		
		
		
	}
	
	
	
	public void write (OutputStream outStream) {
		PrintStream out = new PrintStream(outStream);

		
		out.println(";Scope: "+ scope);

		
		//
		// Only for changing/adding new option to the generated SMT file
		//
//		out.println("(set-option :auto-config false)");
//		out.println("(set-option :mbqi false)");
		//out.println("(set-option :ematching true)");
		
		if(defaultLogic!=null && scope==null){
			out.println("(set-logic "+defaultLogic+")");
		}
		else if (scope == null)
			out.println("(set-logic AUFLIA)");
		else
			out.println("(set-logic UFBV)");
		
		

		
//		out.println("(set-option :macro-finder true)");
		
//		
//		out.println("(set-option :case-split 2)");
//		out.println("(set-option :delay-units true)");
//		out.println("(set-option :qi-eager-threshold 100)");
//		out.println("(set-option :restart-strategy 0)");
//		out.println("(set-option :restart-factor 1.5)");
//		out.println("(set-option :auto-config false)");
		
		
		
//		out.println(";(set-option :relevancy 1)");

//		out.println(";(set-option :elim-quantifiers true)");
//		out.println(";(set-option :elim-nlarith-quantifiers true)");
		
//		out.println(";(set-option :pull-nested-quantifiers true)");
//		out.println(";(set-option :model-compact true)");
//		out.println(";(set-option :print-success false)");
		out.println();

		for (SMTSort s : sorts) {
			out.println(s.toString());
		}
		out.println();
		for (SMTFunction func : functions) {
			out.println(func.toString());
		}
		out.println();
		for (SMTTerm form : formulas) {
			if(form != SMTTerm.TRUE) {
				out.println("(assert ");
				out.println(form.toString(1));
				out.println(")");
				out.println();
			}
		}
		
		
		out.println();
		out.println("(check-sat)");
		out.println(";(get-model)");
		out.println("(exit)");
		
	}
	
	
}
