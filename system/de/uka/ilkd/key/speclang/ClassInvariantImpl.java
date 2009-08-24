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
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;


/**
 * Standard implementation of the ClassInvariant interface. 
 */
public final class ClassInvariantImpl implements ClassInvariant {
    
    private static final SignatureVariablesFactory SVN 
        = SignatureVariablesFactory.INSTANCE;
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final String name;
    private final String displayName;
    private final KeYJavaType kjt;
    private final Term originalInv;
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
                              Term inv,
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
        
        if(selfVar != null && originalSelfVar != null) {
            assert selfVar.sort().extendsTrans(originalSelfVar.sort());
            result.put(originalSelfVar, selfVar);
        }

        return result;
    }
    
    
    /**
     * Returns an available name constructed by affixing a counter to the passed 
     * base name.
     */
    private String getNewName(String baseName, Services services) {
        NamespaceSet namespaces = services.getNamespaces();
            
        int i = 0;
        String result;
        do {
            result = baseName + "_" + i++;
        } while(namespaces.lookup(new Name(result)) != null);
        
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
    

    public Term getClosedInv(Services services) {
        Sort sort = getKJT().getSort();
        String baseName = sort.name().toString().substring(0, 1).toLowerCase();
        String fullName = getNewName(baseName, services);
        LogicVariable selfVar = new LogicVariable(new Name(fullName), sort);
        return TB.allClose(getOpenInv(selfVar, services));
    }
    
    
    public Term getClosedInvExcludingOne(ParsableVariable excludedVar, 
	                                 Services services) {
        Sort sort = getKJT().getSort();
        String baseName = sort.name().toString().substring(0, 1).toLowerCase();
        String fullName = getNewName(baseName, services);
        LogicVariable quantifVar = new LogicVariable(new Name(fullName), sort);
        Term openInv = getOpenInv(quantifVar, services);
        Term notSelf = TB.not(TB.equals(TB.var(quantifVar), 
        	                        TB.var(excludedVar)));        
        return TB.allClose(TB.imp(notSelf, openInv));
    }
    
    
    public Term getOpenInv(ParsableVariable selfVar, Services services) {
        final Map<Operator, Operator> replaceMap = getReplaceMap(selfVar, services);
        final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalInv);   
    }

    
    public String getHTMLText(Services services) {
        final String inv = LogicPrinter.quickPrintTerm(originalInv, 
                services);
        
        return "<html>"
               + LogicPrinter.escapeHTML(inv) 
               + "</html>";
    }
    
    
    public String toString() {
        return originalInv.toString();
    }
}
