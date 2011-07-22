// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


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
    private JMLSpecFactory sf;
    private Services services;
    
    
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
                @SuppressWarnings("hiding") Services services) {
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
    public Term getClause(ParsableVariable selfVar, @SuppressWarnings("hiding") Services services) {
        final Map<Operator, Operator> replaceMap 
        	= getReplaceMap(selfVar, services);
        final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalInv);   
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
	res.setSpecFactory(sf,services);
	return res;
    }
    
    // HACK
    public void setSpecFactory(JMLSpecFactory sf, Services s){
	this.sf = sf;
	services = s;
    }
    
    
    private ImmutableList<PositionedString> createPrecond(ProgramMethod pm){
	ImmutableList<PositionedString> res = ImmutableSLList.<PositionedString>nil();
	for (ParameterDeclaration p: pm.getMethodDeclaration().getParameters()){
	    if (!JMLInfoExtractor.parameterIsNullable(pm, p)) {
		res = res.append(createNonNullPositionedString(p.getVariableSpecification().getName(), p.getVariableSpecification().getProgramVariable().getKeYJavaType(), false, originalSpec.fileName, originalSpec.pos));
	    }
	}
	return res;
    }
    
    /**
     * creates a JML specification expressing that the given variable/field is not null and in case of a reference
     * array type that also its elements are non-null 
     * In case of implicit fields or primitive typed fields/variables the empty set is returned 
     * @param varName the String specifying the variable/field name
     * @param kjt1 the KeYJavaType representing the variables/field declared type
     * @param isImplicitVar a boolean indicating if the the field is an implicit one (in which case no 
     * @param fileName the String containing the filename where the field/variable has been declared
     * @param pos the Position where to place this implicit specification
     * @return set of formulas specifying non-nullity for field/variables
     */  
    private ImmutableList<PositionedString> createNonNullPositionedString(String varName, KeYJavaType kjt1, 
	    boolean isImplicitVar, String fileName, Position pos) {
	ImmutableList<PositionedString> result = ImmutableSLList.<PositionedString>nil(); 
	final Type varType  = kjt1.getJavaType(); 

	
	if (services.getTypeConverter().isReferenceType(varType) && !isImplicitVar) {

	    PositionedString ps 
	    = new PositionedString(varName + " != null", fileName, pos);
	    result = result.append(ps);
	    if (varType instanceof ArrayType && 
		    services.getTypeConverter().
		    isReferenceType(((ArrayType)varType).getBaseType().getKeYJavaType())) {
		final PositionedString arrayElementsNonNull 
		= new PositionedString("(\\forall int i; 0 <= i && i < " + varName + ".length;" 
			+ varName + "[i]" + " != null)", 
			fileName, 
			pos);
		result = result.append(arrayElementsNonNull);
	    }
	}
	return result;
    }

    
    @Override
    public ImmutableSet<Contract> toContract(ProgramMethod pm) { 
        try {
            if (sf==null) throw new SLTranslationException("Contract for initially clause could not be created because no SpecFactory given");
            if (! pm.isConstructor()) throw new SLTranslationException("Initially clauses only apply to constructors, not to method "+pm);
            final TextualJMLSpecCase specCase =
                new TextualJMLSpecCase(ImmutableSLList.<String>nil(),
                        Behavior.NONE);
            specCase.addName(new PositionedString(getName()));
            specCase.addRequires(createPrecond(pm));
            specCase.addEnsures(originalSpec);
            specCase.addSignals(originalSpec);
            specCase.addDiverges(new PositionedString("true"));
            return sf.createJMLOperationContracts(pm, specCase);
        } catch (SLTranslationException e){ 
            services.getExceptionHandler().reportException(e);
            return null;
        }
    }
}
