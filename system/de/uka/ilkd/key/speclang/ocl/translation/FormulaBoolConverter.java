//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.ListOfLogicVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SLListOfLogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Converts between formulas and boolean terms.
 */
class FormulaBoolConverter {
    private static final String VARNAME_PREFIX = "_oclFBC";
    private static final TermBuilder tb = TermBuilder.DF;

    private final NamespaceSet nss;
    private final Term trueLitTerm;
    private final Sort boolSort;
    
    private int varCounter = 0;
    private ListOfTerm termsToAdd = SLListOfTerm.EMPTY_LIST;
    private ListOfLogicVariable introducedVars 
                                  = SLListOfLogicVariable.EMPTY_LIST;
    
    
    /**
     * @param serv used for adding the created variables to the 
     * appropriate namespace
     * 
     */
    public FormulaBoolConverter(Services serv, NamespaceSet nss) {
        this.nss = nss;
        trueLitTerm = serv.getTypeConverter()
                                .convertToLogicElement(BooleanLiteral.TRUE);
        boolSort    = serv.getJavaInfo()
                                .getKeYJavaType(PrimitiveType.JAVA_BOOLEAN)
                                .getSort();
    }
    
    /**
     * Sets the counter which is used for naming the introduced variables.
     */
    public void setVariableCounter(int value) {
        varCounter = value;
    }
    
    
    /**
     * Returns the current value of the counter which is used for naming the 
     * introduced variables.
     */
    public int getVariableCounter() {
        return varCounter;
    }
    
    
    /**
     * Adds axiomatisations for all variables which have been introduced so far 
     * to a term. 
     * 
     */
    public Term addAxioms(Term term) {
        Term result = term;
        
        Term termToAdd = null;
        if(termsToAdd.size() == 1) {
            termToAdd = termsToAdd.head();
        } else if(termsToAdd.size() > 1) {
            termToAdd = tb.and(termsToAdd.toArray());
        }
        
        if(termToAdd != null) {
            Term impTerm = tb.imp(termToAdd, result);
            result = tb.all(introducedVars.toArray(), impTerm);
        } 
        
        return result;
    }
    
    
    /**
     * Converts a term to a formula, if it is boolean; otherwise, just returns 
     * the term unchanged.
     */
    public Term convertBoolToFormula(Term term) {
        Term result = term;
        
        if(term != null && term.sort() == boolSort) {
            result = tb.equals(term, trueLitTerm);
        }
        
        return result;
    }


    /**
     * Converts a term to a boolean term, if it is a formula; otherwise, just 
     * returns the term unchanged. For the conversion, a logic variable is
     * introduced, which must later be axiomatised by calling addAxioms(). 
     */
    public Term convertFormulaToBool(Term term) {
        Term result = term;
        
        if(term != null && term.sort() == Sort.FORMULA) {
            Name name = new Name(VARNAME_PREFIX + varCounter++);
            LogicVariable var = new LogicVariable(name, boolSort);
            
            nss.variables().add(var);
            introducedVars = introducedVars.prepend(var);
            
            Term varTerm = tb.var(var);
            Term varTrueTerm = tb.equals(varTerm,trueLitTerm);
            Term termToAdd = tb.equiv(term,varTrueTerm);
            
            termsToAdd = termsToAdd.append(termToAdd);
            
            result = varTerm;
        }
        
        return result;
    }


    /**
     * Converts those terms in a list which are formulas to boolean 
     * terms, and leaves the others unchanged.
     */
    public ListOfTerm convertFormulasToBool(ListOfTerm list) {
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;
        
        IteratorOfTerm it = list.iterator();
        while(it.hasNext()) {
            result = result.append(convertFormulaToBool(it.next()));
        }
        
        return result;
    }


    /**
     * Converts those terms in a list of OCLEntities which are formulas 
     * to boolean terms, and leaves the others unchanged.
     */
    public ListOfTerm convertFormulasToBool(ListOfOCLEntity list) {
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;
        
        IteratorOfOCLEntity it = list.iterator();
        while(it.hasNext()) {
            result = result.append(it.next().getTerm());
        }
        
        return convertFormulasToBool(result);
    }

}
