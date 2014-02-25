// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.proof.OpReplacer;


/**
 * Standard implementation of the InitiallyClause interface.
 * @author Daniel Bruns 
 */
public final class InitiallyClauseImpl implements InitiallyClause {
        
    private final String name;
    private final String displayName;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;    
    private final Term originalInv;
    private final ParsableVariable originalSelfVar;
    private final PositionedString originalSpec;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 

    /**
     * Creates a class invariant.
     * @param name the unique internal name of the invariant
     * @param displayName the displayed name of the invariant
     * @param kjt the KeYJavaType to which the invariant belongs
     * @param visibility the visibility of the invariant 
     *        (null for default visibility)
     * @param inv the invariant formula itself
     * @param selfVar the variable used for the receiver object
     */
    public InitiallyClauseImpl(String name, 
                              String displayName,
                              KeYJavaType kjt, 
                              VisibilityModifier visibility,                              
                              Term inv,
                              ParsableVariable selfVar, PositionedString originalSpec) {
        assert name != null && !name.equals("");
        assert displayName != null && !displayName.equals("");
	assert kjt != null;
        assert inv != null;
        this.name            = name;
        this.displayName     = displayName;
	this.kjt             = kjt;
        this.visibility      = visibility;
        this.originalInv     = inv;
        this.originalSelfVar = selfVar;
        final OpCollector oc = new OpCollector();
        originalInv.execPostOrder(oc);
        this.originalSpec = originalSpec;
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    private Map<Operator, Operator> getReplaceMap(
                ParsableVariable selfVar, 
                TermServices services) {
        Map<Operator, Operator> result = new LinkedHashMap<Operator, Operator>();
        
        if(selfVar != null && originalSelfVar != null) {
            assert selfVar.sort().extendsTrans(originalSelfVar.sort());
            result.put(originalSelfVar, selfVar);
        }

        return result;
    }
    

    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    @Override
    public String getName() {
        return name;
    }
    
    
    @Override
    public String getDisplayName() {
        return displayName;
    }
    
        
    @Override
    public KeYJavaType getKJT() {
	return kjt;
    }
    
    
    @Override
    public Term getClause(ParsableVariable selfVar, TermServices services) {
        final Map<Operator, Operator> replaceMap 
        	= getReplaceMap(selfVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        Term res = or.replace(originalInv);
        res = services.getTermBuilder().convertToFormula(res);
        return res;
    }
     
    @Override
    public PositionedString getOriginalSpec(){
        return originalSpec;
    }
    
    @Override
    public VisibilityModifier getVisibility() {
	return visibility;
    }
    
    
    
    
    @Override
    public String toString() {
        return originalInv.toString();
    }
    
    @Override
    public InitiallyClause setKJT(KeYJavaType newKjt) {
	InitiallyClauseImpl res= new InitiallyClauseImpl(name, 
                                      displayName,
                                      newKjt, 
                                      visibility,
                                      originalInv,
                                      originalSelfVar,originalSpec);
	return res;
    }
    

}
