// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;


/**
 * Standard implementation of the ClassInvariant interface. 
 */
public class ClassInvariantImpl implements ClassInvariant {
    
    protected static final SignatureVariablesFactory SVN 
        = SignatureVariablesFactory.INSTANCE;
    
    private final String name;
    private final String displayName;
    private final KeYJavaType kjt;
    private final FormulaWithAxioms originalInv;
    private final ParsableVariable originalSelfVar;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 

    /**
     * Creates a class invariant.
     * @param name the unique internal name of the invariant
     * @param displayName the displayed name of the invariant
     * @param kjt the KeYJavaType to which the invariant belongs
     * @param inv the invariant formula itself
     * @param selfVar the variable used for the receiver object
     */
    public ClassInvariantImpl(String name, 
                              String displayName,
                              KeYJavaType kjt, 
                              FormulaWithAxioms inv,
                              ParsableVariable selfVar) {
        assert name != null && !name.equals("");
        assert displayName != null && !displayName.equals("");
	assert kjt != null;
        assert inv != null;
        this.name            = name;
        this.displayName     = displayName;
	this.kjt             = kjt;
        this.originalInv     = inv;
        this.originalSelfVar = selfVar;
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    private Map<Operator, Operator> getReplaceMap(
                ParsableVariable selfVar, 
                Services services) {
        Map<Operator, Operator> result = new LinkedHashMap<Operator, Operator>();
        
        if(selfVar != null) {
            assert selfVar.sort().extendsTrans(originalSelfVar.sort());
            result.put(originalSelfVar, selfVar);
        }

        return result;
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    public String getName() {
        return name;
    }
    
    
    public String getDisplayName() {
        return displayName;
    }
    
        
    public KeYJavaType getKJT() {
	return kjt;
    }    
    

    public FormulaWithAxioms getClosedInv(Services services) {
        Sort sort = getKJT().getSort();
        String name = sort.name().toString().substring(0, 1).toLowerCase();
        LogicVariable selfVar = new LogicVariable(new Name(name), sort);
        return getOpenInv(selfVar, services).allClose(services);
    }
  
    
    public FormulaWithAxioms getOpenInv(ParsableVariable selfVar, 
                                        Services services) {
        final Map<Operator, Operator> replaceMap = getReplaceMap(selfVar, services);
        final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalInv);   
    }

    
    public String getHTMLText(Services services) {
        final String inv = LogicPrinter.quickPrintTerm(originalInv.getFormula(), 
                services);
        
        return "<html>"
               + LogicPrinter.escapeHTML(inv) 
               + "</html>";
    }
    
    
    public String toString() {
        return originalInv.toString();
    }
}
