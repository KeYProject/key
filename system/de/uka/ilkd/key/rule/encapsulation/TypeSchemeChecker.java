// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;

import java.util.Map;

import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;


class TypeSchemeChecker {

    private static final TypeSchemeTerm DEFAULT_FIELD_TERM
                = TypeSchemeUnion.ROOT;

    private final Map /*Location -> TypeSchemeTerm*/ annotations;
    private ListOfTypeSchemeConstraint constraints
                = SLListOfTypeSchemeConstraint.EMPTY_LIST;
    private boolean failed = false;

    private int stringLitNameCounter   = 0;
    private int allocNameCounter       = 0;
    private int arrayAllocNameCounter  = 0;
    private int conditionalNameCounter = 0;


    public TypeSchemeChecker(Map /*Location -> TypeSchemeTerm*/
                                 annotations) {
        this.annotations = annotations;
    }


    
    //-------------------------------------------------------------------------
    //internal helper methods
    //-------------------------------------------------------------------------
    
    private void verbose(Object o) {
        //System.out.println(o);
    }
                

    private void addConstraint(TypeSchemeConstraint constraint) {
        verbose("Adding constraint: " + constraint);
        constraints = constraints.prepend(constraint);
    }
    
    
    private void addSubConstraint(TypeSchemeTerm term1, 
                                  TypeSchemeTerm term2) {
        addConstraint(new TypeSchemeSubConstraint(term1, term2));
    }
    
    
    private void addEqualConstraint(TypeSchemeTerm term1, 
                                    TypeSchemeTerm term2) {
        addConstraint(new TypeSchemeEqualConstraint(term1, term2));
    }

    
    private boolean hasPrimitiveType(ProgramVariable pv) {
        return !(pv.sort() instanceof ObjectSort);
    }

    
    private ListOfTypeSchemeConstraint dropTriviallyTrueConstraints(
                                                ListOfTypeSchemeConstraint c) {
        ListOfTypeSchemeConstraint result
                        = SLListOfTypeSchemeConstraint.EMPTY_LIST;
                        
        IteratorOfTypeSchemeConstraint it = c.iterator();
        while(it.hasNext()) {
            TypeSchemeConstraint constraint = it.next();
            if(constraint.getFreeVars().size() > 0 || !constraint.evaluate()) {
                result = result.prepend(constraint);
            }
        }

        return result;
    }
    
        

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public void fail() {
        failed = true;
    }

     
    public ListOfTypeSchemeConstraint getConstraints() {
        if(failed) {
            TypeSchemeConstraint fc = new TypeSchemeFalseConstraint();
            return SLListOfTypeSchemeConstraint.EMPTY_LIST.append(fc);
        } else {
            return dropTriviallyTrueConstraints(constraints);
        }
    }
    
    
    public TypeSchemeTerm checkNull() {
        return TypeSchemeUnion.NULL;
    }
    
    
    public TypeSchemeTerm checkThis() {
        return TypeSchemeUnion.THIS;
    }


    public TypeSchemeTerm checkSuper() {
        return TypeSchemeUnion.THIS;
    }

    
    public TypeSchemeTerm checkStringLiteral() {
        return new TypeSchemeVariable("TS(stringliteral"
                                        + stringLitNameCounter++ + ")",
                                      TypeSchemeUnion.REP_PEER_ROOT);
    }


    public TypeSchemeTerm checkPrimitiveLiteral() {
        return TypeSchemeUnion.PRIMITIVE;
    }


    public TypeSchemeTerm checkPrimitiveUnary(TypeSchemeTerm operandTerm) {
        return TypeSchemeUnion.PRIMITIVE;
    }


    public TypeSchemeTerm checkPrimitiveBinary(TypeSchemeTerm operandTerm1,
                                               TypeSchemeTerm operandTerm2) {
        return TypeSchemeUnion.PRIMITIVE;
    }
    
    
    public TypeSchemeTerm checkInstanceLocalVariable(ProgramVariable var) {
        TypeSchemeTerm varTerm;
        
        if(hasPrimitiveType(var)) {
            varTerm = TypeSchemeUnion.PRIMITIVE;
        } else {
            varTerm = (TypeSchemeTerm) annotations.get(var);
        
            if(varTerm == null) {
                varTerm = new TypeSchemeVariable(
                                        "TS(" + var + ")", 
                                        TypeSchemeUnion.REP_PEER_READONLY_ROOT);
                annotations.put(var, varTerm);
            } else {
                Debug.assertTrue(((TypeSchemeVariable)varTerm).getDefaultValue()
                                 == TypeSchemeUnion.REP_PEER_READONLY_ROOT);
            }
        }
        
        return varTerm;
    }
    
    
    public TypeSchemeTerm checkStaticLocalVariable(ProgramVariable var) {
        TypeSchemeTerm varTerm;
        
        if(hasPrimitiveType(var)) {
            varTerm = TypeSchemeUnion.PRIMITIVE;
        } else {
            varTerm = (TypeSchemeTerm) annotations.get(var);
            
            if(varTerm == null) {
                varTerm = new TypeSchemeVariable("TS(" + var + ")",
                                                 TypeSchemeUnion.READONLY_ROOT);
                annotations.put(var, varTerm);
            } else {
                Debug.assertTrue(((TypeSchemeVariable)varTerm).getDefaultValue()
                                 == TypeSchemeUnion.READONLY_ROOT);

            }
        }
        
        return varTerm;
    }
    
    
    public TypeSchemeTerm checkInstanceField(ProgramVariable field) {
        TypeSchemeTerm fieldTerm;
        
        if(hasPrimitiveType(field)) {  
            fieldTerm = TypeSchemeUnion.PRIMITIVE;     
        } else {
            fieldTerm = (TypeSchemeTerm) annotations.get(field);
         
            if(fieldTerm == null) {
                fieldTerm = DEFAULT_FIELD_TERM;
            }
        }
        
        return fieldTerm;
    }
    
    
    public TypeSchemeTerm checkStaticField(ProgramVariable field) {
        TypeSchemeTerm fieldTerm;
        
        if(hasPrimitiveType(field)) {       
            fieldTerm = TypeSchemeUnion.PRIMITIVE;
        } else {
            fieldTerm = (TypeSchemeTerm) annotations.get(field);
         
            if(fieldTerm == null) {
                fieldTerm = DEFAULT_FIELD_TERM;
            }
            
            addEqualConstraint(fieldTerm, TypeSchemeUnion.READONLY_ROOT);
        }

        return fieldTerm;
    }
      
    
    public TypeSchemeTerm checkInstanceFieldAccess(
                                                TypeSchemeTerm receiverTerm,
                                                TypeSchemeTerm fieldTerm) {
        return new TypeSchemeCombineTerm(receiverTerm, fieldTerm);
    }
    
    
    public TypeSchemeTerm checkStaticFieldAccess(TypeSchemeTerm fieldTerm) {
        return fieldTerm;
    }


    public TypeSchemeTerm checkArrayAccess(Sort arraySort,
                                           TypeSchemeTerm receiverTerm,
                                           TypeSchemeTerm positionTerm) {
        ArrayOp arrayOp = ArrayOp.getArrayOp(arraySort);
        Debug.assertTrue(arrayOp != null);
        TypeSchemeTerm componentTerm
                        = (TypeSchemeTerm) annotations.get(arrayOp);

        if(componentTerm == null) {
            componentTerm = DEFAULT_FIELD_TERM;
        }

        return new TypeSchemeCombineTerm(receiverTerm, componentTerm);
    }
    
        
    public TypeSchemeTerm checkInstanceMethodCall(
                                            TypeSchemeTerm receiverTerm,
                                            TypeSchemeTerm[] actualParTerms,
                                            TypeSchemeTerm[] formalParTerms,
                                            TypeSchemeTerm formalResultTerm) {
        Debug.assertTrue(actualParTerms.length == formalParTerms.length);
        
        for(int i = 0; i < formalParTerms.length; i++) {
            TypeSchemeTerm recFormalParTerm 
                        = new TypeSchemeCombineTerm(receiverTerm, 
                                                    formalParTerms[i]);
            addSubConstraint(actualParTerms[i], recFormalParTerm);
        }
        
        return (formalResultTerm == null
                ? null
                : new TypeSchemeCombineTerm(receiverTerm, formalResultTerm));
            
    }
    
    
    public TypeSchemeTerm checkStaticMethodCall(
                                            TypeSchemeTerm[] actualParTerms,
                                            TypeSchemeTerm[] formalParTerms,
                                            TypeSchemeTerm formalResultTerm) {
        Debug.assertTrue(actualParTerms.length == formalParTerms.length);
        
        for(int i = 0; i < formalParTerms.length; i++) {
            addSubConstraint(actualParTerms[i], formalParTerms[i]);
        }
        
        return formalResultTerm;
    }
    
    
    public TypeSchemeTerm checkAllocation(TypeSchemeTerm[] actualParTerms,
                                          TypeSchemeTerm[] formalParTerms) {
        Debug.assertTrue(actualParTerms.length == formalParTerms.length);
        
        TypeSchemeTerm newTerm 
                        = new TypeSchemeVariable("TS(allocation"
                                                   + allocNameCounter++ + ")",
                                                 TypeSchemeUnion.REP_PEER_ROOT);
        
        for(int i = 0; i < formalParTerms.length; i++) {
            TypeSchemeTerm newFormalParTerm 
                        = new TypeSchemeCombineTerm(newTerm, formalParTerms[i]);
            addSubConstraint(actualParTerms[i], newFormalParTerm);
        }
        
        return newTerm;
    }


    public TypeSchemeTerm checkArrayAllocation(TypeSchemeTerm sizeTerm) {
        return new TypeSchemeVariable("TS(arrayallocation"
                                        + arrayAllocNameCounter++ + ")",
                                      TypeSchemeUnion.REP_PEER_ROOT);
    }


    public TypeSchemeTerm checkConditional(TypeSchemeTerm conditionTerm,
                                           TypeSchemeTerm thenTerm,
                                           TypeSchemeTerm elseTerm) { 
        TypeSchemeTerm conditionalTerm
                = new TypeSchemeVariable(
                             "TS(conditional" + conditionalNameCounter++ + ")",
                             TypeSchemeUnion.PRIMITIVE_REP_PEER_READONLY_ROOT);

        addSubConstraint(thenTerm, conditionalTerm);
        addSubConstraint(elseTerm, conditionalTerm);
        
        return conditionalTerm;
    }

    
    public TypeSchemeTerm checkAssignment(TypeSchemeTerm lhsTerm,
                                          TypeSchemeTerm rhsTerm) {
        addSubConstraint(rhsTerm, lhsTerm);
        return lhsTerm;
    }
    
    
    public void checkReturn(TypeSchemeTerm actualResultTerm,
                            TypeSchemeTerm formalResultTerm) {
        Debug.assertTrue((actualResultTerm == null) 
                         == (formalResultTerm == null));
        if(actualResultTerm != null) {
            addSubConstraint(actualResultTerm, formalResultTerm);
        }
    }
    
    
    public void checkCatch(TypeSchemeTerm excTerm) {
        addEqualConstraint(excTerm, TypeSchemeUnion.READONLY);
    }
}
