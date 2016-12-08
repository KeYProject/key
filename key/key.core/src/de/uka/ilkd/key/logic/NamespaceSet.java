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

package de.uka.ilkd.key.logic;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RuleSet;

public class NamespaceSet {

    private Namespace<QuantifiableVariable> varNS = new Namespace<QuantifiableVariable>();
    private Namespace<IProgramVariable> progVarNS = new Namespace<IProgramVariable>();
    private Namespace<Operator> funcNS = new Namespace<Operator>();
    private Namespace<RuleSet> ruleSetNS = new Namespace<RuleSet>();
    private Namespace<Sort> sortNS = new Namespace<Sort>();
    private Namespace<Choice> choiceNS = new Namespace<Choice>();

    public NamespaceSet() {
    }

    public NamespaceSet(Namespace<QuantifiableVariable> varNS, 
	    		Namespace<Operator> funcNS, 
                        Namespace<Sort> sortNS, 
                        Namespace<RuleSet> ruleSetNS,
			Namespace<Choice> choiceNS, 
			Namespace<IProgramVariable> programVarNS) {
	this.varNS     = varNS;
	this.progVarNS = programVarNS;
	this.funcNS    = funcNS;
	this.sortNS    = sortNS;
	this.ruleSetNS = ruleSetNS;
	this.choiceNS  = choiceNS;
    }

    public Namespace<QuantifiableVariable> variables() {
	return varNS;
    }

    public void setVariables(Namespace<QuantifiableVariable> varNS) {
	this.varNS = varNS;
    }

    public Namespace<IProgramVariable> programVariables() {
	return progVarNS;
    }

    public void setProgramVariables(Namespace<IProgramVariable> progVarNS) {
	this.progVarNS = progVarNS;
    }

    public Namespace<Operator> functions() {
	return funcNS;
    }

    public void setFunctions(Namespace<Operator> funcNS) {
	this.funcNS = funcNS;
    }

    public Namespace<RuleSet> ruleSets() {
	return ruleSetNS;
    }

    public void setRuleSets(Namespace<RuleSet> ruleSetNS) {
	this.ruleSetNS = ruleSetNS;
    }

    public Namespace<Sort> sorts() {
	return sortNS;
    }

    public void setSorts(Namespace<Sort> sortNS) {
	this.sortNS = sortNS;
    }

    public Namespace<Choice> choices() {
	return choiceNS;
    }

    public void setChoices(Namespace<Choice> choiceNS) {
	this.choiceNS = choiceNS;
    }
    
    public void add(NamespaceSet ns) {
	variables().add(ns.variables());
	programVariables().add(ns.programVariables());
	sorts().add(ns.sorts());
	ruleSets().add(ns.ruleSets());
	functions().add(ns.functions());
	choices().add(ns.choices());
    }

    public NamespaceSet copy() {
	NamespaceSet c = new NamespaceSet();
	c.setSorts(sorts().copy());
	c.setRuleSets(ruleSets().copy());
	c.setFunctions(functions().copy());
	c.setVariables(variables().copy());
	c.setProgramVariables(programVariables().copy());
	c.setChoices(choices().copy());
	return c;
    }
    
    /**
     * starts the protocol of all contained namespaces
     */
    public void startProtocol() {
	variables().startProtocol();
	programVariables().startProtocol();
	sorts().startProtocol();
	ruleSets().startProtocol();
	functions().startProtocol();
	choices().startProtocol();
    }
       
    /**
     * returns all namespaces in an array     
     */
    private Namespace<?>[] asArray() {
        return new Namespace[]{variables(), 
        		       programVariables(), 
        		       sorts(), 
        		       ruleSets(), 
        		       functions(),
        		       choices()
        };
    }
    
    /**
     * returns all namespaces with symbols that may occur
     * in a real sequent (this means all namespaces without
     * variables, choices and ruleSets)      
     */
    private Namespace<?>[] logicAsArray() {
        return new Namespace[]{
           programVariables(), sorts(), functions()
        };
    }
    
    /**
     * adds the protocolled names of the given NamespaceSet to this one    
     */
    @SuppressWarnings({ "rawtypes", "unchecked" })
    @Deprecated 
    public void addProtocolled(NamespaceSet nss) {
      final Namespace[] myNames = asArray();
      final Namespace[] otherNames = nss.asArray();
      for (int i = 0; i<myNames.length; i++) {
          final Iterator<Named> it = otherNames[i].getProtocolled();
          while (it.hasNext()) {
              myNames[i].add(it.next());
          }
      }       
    }

    /**
     * looks up if the given name is found in one of the namespaces
     * and returns the named object or null if no object with the same name 
     * has been found
     */
    public Named lookup(Name name) {
	final Namespace[] spaces = asArray();
	return lookup(name, spaces);
    }

    /**
     * looks up for the symbol in the namespaces sort, functions and
     * programVariables
     * @param name the Name to look up
     * @return the element of the given name or null
     */
    public Named lookupLogicSymbol(Name name) {        
        return lookup(name, logicAsArray());
    }
    
    /**
     * @param name
     * @param spaces
     * @return the element with the given name if found in the 
     * given namespaces, otherwise <tt>null</tt>
     */
    private Named lookup(Name name, final Namespace[] spaces) {
        for (Namespace<?> space : spaces) {
            final Named n = space.lookup(name);
            if (n != null) return n;
        } 
        return null;
    }

    
    @Override
    public String toString() {
	return "Sorts: " + sorts() + "\n" +
	    "Functions: " + functions() + "\n" +
	    "Variables: " + variables() + "\n" +
	    "ProgramVariables: " + programVariables() + "\n" +
	    "Heuristics: " + ruleSets() + "\n" +
	    "Taclet Options: " + choices() + "\n";
    }
    
    
    public <T extends Name> boolean contains(ImmutableSet<T> names) {
        for (Name name : names) {
            if (lookupLogicSymbol(name) == null) {
                return false;
            }
        }
        return true;
    }
    
    public void seal() {
        varNS.seal();
        progVarNS.seal();
        funcNS.seal();
        ruleSetNS.seal();
        sortNS.seal();
        choiceNS.seal();
    }
    
}
