//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml.translation;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayOfVariableSpecification;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.EverythingLocationDescriptor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetAsListOfTerm;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ListOfLogicVariable;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SLListOfParsableVariable;
import de.uka.ilkd.key.logic.op.SetAsListOfProgramMethod;
import de.uka.ilkd.key.logic.op.SetOfProgramMethod;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.ListOfPositionedString;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.OperationContractImpl;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SetAsListOfOperationContract;
import de.uka.ilkd.key.speclang.SetOfOperationContract;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassInv;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * A factory for creating class invariants and operation contracts
 * from textual JML specifications. This is the public interface to the 
 * jml.translation package.
 */
public class JMLSpecFactory {
    
    private static final TermBuilder TB
            = TermBuilder.DF;
    private static final SignatureVariablesFactory SVF 
            = SignatureVariablesFactory.INSTANCE;
    
    private final Services services;
    private final JMLTranslator translator;
    
    private int invCounter;
    private int contractCounter;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
  
    public JMLSpecFactory(Services services) {
        assert services != null;
        this.services = services;
        this.translator = new JMLTranslator(services);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private String getInvName() {
        return "JML class invariant (id: " + invCounter++ + ")";
    }
    
    
    private String getContractName(Behavior behavior) {
        return "JML " 
               + behavior 
               + "operation contract (id: " + contractCounter++ + ")";
    }
    
    
    private SetOfProgramMethod getOverridingMethods(ProgramMethod pm) {
        JavaInfo ji = services.getJavaInfo();
        String name   = pm.getMethodDeclaration().getName();
        int numParams = pm.getParameterDeclarationCount();
        SetOfProgramMethod result = SetAsListOfProgramMethod.EMPTY_SET;
        
        KeYJavaType kjt = pm.getContainerType();
        assert kjt != null;
        for(KeYJavaType sub : ji.getAllSubtypes(kjt)) {
            assert sub != null;
            
            ListOfProgramMethod subPms 
                = ji.getAllProgramMethodsLocallyDeclared(sub);
            for(ProgramMethod subPm : subPms) {
                if(subPm.getMethodDeclaration().getName().equals(name) 
                   && subPm.getParameterDeclarationCount() == numParams) {
                    boolean paramsEqual = true;
                    for(int i = 0; i < numParams; i++) {
                        if(!subPm.getParameterType(i)
                                 .equals(pm.getParameterType(i))) {
                            paramsEqual = false;
                            break;
                        }
                    }
                    
                    if(paramsEqual) {
                        result = result.add(subPm);
                    }
                }
            }
        }
        
        return result;
    }
    
    
    /**
     * Collects local variables of the passed statement that are visible for 
     * the passed loop. Returns null if the loop has not been found.
     */
    private ListOfParsableVariable collectLocalVariables(StatementContainer sc, 
                                                         LoopStatement loop){
        ListOfParsableVariable result = SLListOfParsableVariable.EMPTY_LIST;
        for(int i = 0, m = sc.getStatementCount(); i < m; i++) {
            Statement s = sc.getStatementAt(i);
            
            if(s instanceof For) {
        	ArrayOfVariableSpecification avs 
        		= ((For)s).getVariablesInScope();
        	for(int j = 0, n = avs.size(); j < n; j++) {
        	    VariableSpecification vs = avs.getVariableSpecification(j);
        	    ProgramVariable pv 
        	    	= (ProgramVariable) vs.getProgramVariable();
        	    result = result.prepend(pv);
        	}
            }

            if(s == loop) {
                return result;
            } else if(s instanceof LocalVariableDeclaration) {
                ArrayOfVariableSpecification vars = 
                    ((LocalVariableDeclaration) s).getVariables();
                for(int j = 0, n = vars.size(); j < n; j++) {
                    ProgramVariable pv 
                        = (ProgramVariable) vars.getVariableSpecification(j)
                                                .getProgramVariable();
                    result = result.prepend(pv);
                }
            } else if(s instanceof StatementContainer) {
                ListOfParsableVariable lpv 
                    = collectLocalVariables((StatementContainer) s, loop);
                if(lpv != null){ 
                    result = result.prepend(lpv);
                    return result;
                }
            } else if(s instanceof BranchStatement) {
                BranchStatement bs = (BranchStatement) s;
                for(int j = 0, n = bs.getBranchCount(); j < n; j++) {
                    ListOfParsableVariable lpv 
                        = collectLocalVariables(bs.getBranchAt(j), loop);
                    if(lpv != null){ 
                        result = result.prepend(lpv);
                        return result;
                    }
                }
            }
        }
        return null;
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
       
    public ClassInvariant createJMLClassInvariant(KeYJavaType kjt, 
                                                  PositionedString originalInv) 
            throws SLTranslationException {
        assert kjt != null;
        assert originalInv != null;
        
        //create variable for self
        Sort sort = kjt.getSort();
        ParsableVariable selfVar = new LogicVariable(new Name("self"), sort);
        
        //translate expression
        FormulaWithAxioms inv = translator.translateExpression(originalInv,
                                                               kjt,
                                                               selfVar,
                                                               null,
                                                               null,
                                                               null,
                                                               null);        
        //create invariant
        String name = getInvName();
        return new ClassInvariantImpl(name,
                                      name,
                                      kjt, 
                                      inv,
                                      selfVar);
    }
    
    
    public ClassInvariant createJMLClassInvariant(
                                        KeYJavaType kjt,
                                        TextualJMLClassInv textualInv) 
            throws SLTranslationException {
        return createJMLClassInvariant(kjt, textualInv.getInv());
    }
    
    
    public SetOfOperationContract createJMLOperationContracts(
                                ProgramMethod programMethod,
                                Behavior originalBehavior,
                                ListOfPositionedString originalRequires,
                                ListOfPositionedString originalAssignable,
                                ListOfPositionedString originalEnsures,
                                ListOfPositionedString originalSignals,
                                ListOfPositionedString originalSignalsOnly,
                                ListOfPositionedString originalDiverges) 
            throws SLTranslationException {
        assert programMethod != null;
        assert originalBehavior != null;
        assert originalRequires != null;
        assert originalEnsures != null;
        assert originalSignals != null;
        assert originalSignalsOnly != null;
        assert originalDiverges != null;
        assert originalAssignable != null;
        
        //create variables for self, parameters, result, exception,
        //and the map for atPre-Functions
        ParsableVariable selfVar = SVF.createSelfVar(services, 
                                                     programMethod, 
                                                     false);
        ListOfParsableVariable paramVars = SVF.createParamVars(services, 
                                                               programMethod, 
                                                               false);
        ParsableVariable resultVar = SVF.createResultVar(services, 
                                                         programMethod, 
                                                         false);
        ParsableVariable excVar = SVF.createExcVar(services,
                                                   programMethod, 
                                                   false);
        Map atPreFunctions = new LinkedHashMap();
        
        //translate requires
        FormulaWithAxioms requires = FormulaWithAxioms.TT;
        for(PositionedString expr : originalRequires) {
            FormulaWithAxioms translated 
                = translator.translateExpression(
                                    expr,
                                    programMethod.getContainerType(),
                                    selfVar, 
                                    paramVars, 
                                    null, 
                                    null,
                                    null);
            requires = requires.conjoin(translated);        
        }
        
        //translate assignable
        SetOfLocationDescriptor assignable;
        if(originalAssignable.isEmpty()) {
            assignable = EverythingLocationDescriptor.INSTANCE_AS_SET;
        } else {
            assignable = SetAsListOfLocationDescriptor.EMPTY_SET;
            for(PositionedString expr : originalAssignable) {
                SetOfLocationDescriptor translated 
                    = translator.translateAssignableExpression(
                                        expr, 
                                        programMethod.getContainerType(),
                                        selfVar, 
                                        paramVars);
                assignable = assignable.union(translated);        
            }
        }
        
        //translate ensures
        FormulaWithAxioms ensures = FormulaWithAxioms.TT;
        for(PositionedString expr : originalEnsures) {
            FormulaWithAxioms translated 
                = translator.translateExpression(
                                    expr,
                                    programMethod.getContainerType(),
                                    selfVar, 
                                    paramVars, 
                                    resultVar, 
                                    excVar,
                                    atPreFunctions);
            ensures = ensures.conjoin(translated);        
        }
        
        //translate signals
        FormulaWithAxioms signals = FormulaWithAxioms.TT;
        for(PositionedString expr : originalSignals) {
            FormulaWithAxioms translated 
                = translator.translateSignalsExpression(
                                    expr, 
                                    programMethod.getContainerType(),
                                    selfVar, 
                                    paramVars, 
                                    resultVar, 
                                    excVar,
                                    atPreFunctions);
            signals = signals.conjoin(translated);        
        }
        
        //translate signals_only
        FormulaWithAxioms signalsOnly = FormulaWithAxioms.TT;
        for(PositionedString expr : originalSignalsOnly) {
            FormulaWithAxioms translated 
                = translator.translateSignalsOnlyExpression(
                                    expr,
                                    programMethod.getContainerType(),
                                    excVar);
            signalsOnly = signalsOnly.conjoin(translated);        
        }
        
        //translate diverges
        FormulaWithAxioms diverges = FormulaWithAxioms.FF;
        for(PositionedString expr : originalDiverges) {
            FormulaWithAxioms translated 
                = translator.translateExpression(
                                    expr, 
                                    programMethod.getContainerType(),
                                    selfVar, 
                                    paramVars, 
                                    null, 
                                    null,
                                    null);
            diverges = diverges.disjoin(translated);        
        }
        
        //translate normal_behavior / exceptional_behavior
        if(originalBehavior == Behavior.NORMAL_BEHAVIOR) {
	    assert originalSignals.isEmpty();
	    assert originalSignalsOnly.isEmpty();
            signals = FormulaWithAxioms.FF;
	    signalsOnly = FormulaWithAxioms.FF;
        } else if(originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR) {
	    assert originalEnsures.isEmpty();
            ensures = FormulaWithAxioms.FF;
        }
        
        //create contract(s)
        SetOfOperationContract result 
            = SetAsListOfOperationContract.EMPTY_SET;
        FormulaWithAxioms excNull 
            = new FormulaWithAxioms(TB.equals(TB.var(excVar), 
                                              TB.NULL(services)));
        FormulaWithAxioms post1 
            = (originalBehavior == Behavior.NORMAL_BEHAVIOR
               ? ensures
	       : excNull.imply(ensures));
        FormulaWithAxioms post2 
            = (originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR
	       ? signals.conjoin(signalsOnly)
	       : excNull.negate().imply(signals.conjoin(signalsOnly)));
        FormulaWithAxioms post 
            = post1.conjoin(post2);
        if(diverges.equals(FormulaWithAxioms.FF)) {
            String name = getContractName(originalBehavior);
            OperationContract contract
                = new OperationContractImpl(name,
                                            name,
                                            programMethod,
                                            Modality.DIA,
                                            requires,
                                            post,
                                            assignable,
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            atPreFunctions); 
            result = result.add(contract);
	} else if(diverges.equals(FormulaWithAxioms.TT)) {
	    String name = getContractName(originalBehavior);
            OperationContract contract
                = new OperationContractImpl(name,
                                            name,
                                            programMethod,
                                            Modality.BOX,
                                            requires,
                                            post,
                                            assignable,
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            atPreFunctions); 
            result = result.add(contract);
        } else {
            String name1 = getContractName(originalBehavior);
            String name2 = getContractName(originalBehavior);
            OperationContract contract1
                = new OperationContractImpl(name1,
                                            name1,
                                            programMethod,
                                            Modality.DIA,
                                            requires.conjoin(diverges.negate()),
                                            post,
                                            assignable,
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            atPreFunctions);
            OperationContract contract2
                = new OperationContractImpl(name2,
                                            name2,
                                            programMethod,
                                            Modality.BOX,
                                            requires,
                                            post,
                                            assignable,
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            atPreFunctions);
            result = result.add(contract1).add(contract2);
        }
        
        return result;
    }
    
    
    public SetOfOperationContract createJMLOperationContracts(
                                        ProgramMethod programMethod,
                                        TextualJMLSpecCase textualSpecCase) 
            throws SLTranslationException {
        return createJMLOperationContracts(
                                    programMethod,
                                    textualSpecCase.getBehavior(),
                                    textualSpecCase.getRequires(),
                                    textualSpecCase.getAssignable(),
                                    textualSpecCase.getEnsures(),
                                    textualSpecCase.getSignals(),
                                    textualSpecCase.getSignalsOnly(),
                                    textualSpecCase.getDiverges());
    }
    
    
    public SetOfOperationContract createJMLOperationContractsAndInherit(
                                        ProgramMethod programMethod,
                                        TextualJMLSpecCase textualSpecCase) 
            throws SLTranslationException {                    
        SetOfOperationContract result 
            = createJMLOperationContracts(programMethod, textualSpecCase);
        
        for(ProgramMethod subPm : getOverridingMethods(programMethod)) {
            SetOfOperationContract subContracts 
                = createJMLOperationContracts(subPm, textualSpecCase);
            result = result.union(subContracts);
        }
        
        return result;
    }
    
    
    public LoopInvariant createJMLLoopInvariant(
                            ProgramMethod programMethod,
                            LoopStatement loop,
                            ListOfPositionedString originalInvariant,
                            ListOfPositionedString originalSkolemDeclarations,
                            ListOfPositionedString originalPredicates,
                            ListOfPositionedString originalAssignable,
                            PositionedString originalVariant) 
            throws SLTranslationException {                
        assert programMethod != null;
        assert loop != null;
        assert originalInvariant != null;
        assert originalSkolemDeclarations != null;
        assert originalPredicates != null;
        assert originalAssignable != null;
        
        //create variables for self, parameters, other relevant local variables 
        //(disguised as parameters to the translator) and the map for 
        //atPre-Functions
        ParsableVariable selfVar = SVF.createSelfVar(services, 
                                                     programMethod, 
                                                     false);
        ListOfParsableVariable paramVars = SLListOfParsableVariable.EMPTY_LIST;
        int numParams = programMethod.getParameterDeclarationCount();
        for(int i = numParams - 1; i >= 0; i--) {
            ParameterDeclaration pd = programMethod.getParameterDeclarationAt(i);
            paramVars = paramVars.prepend((ProgramVariable) 
                                          pd.getVariableSpecification()
                                             .getProgramVariable());
        }

        ListOfParsableVariable localVars 
            = collectLocalVariables(programMethod.getBody(), loop);        
        paramVars = paramVars.append(localVars);
        Map atPreFunctions = new LinkedHashMap();
        
        //translate invariant
        Term invariant;
        if(originalInvariant.isEmpty()) {
            invariant = null;
        } else {
            invariant = TB.tt();
            for(PositionedString expr : originalInvariant) {
                FormulaWithAxioms translated 
                    = translator.translateExpression(
                                            expr, 
                                            programMethod.getContainerType(),
                                            selfVar, 
                                            paramVars, 
                                            null, 
                                            null,
                                            atPreFunctions);
                assert translated.getAxioms().isEmpty();
                invariant = TB.and(invariant, translated.getFormula());
            }
        }
        
        //translate skolem declarations
        ListOfParsableVariable freeVars = SLListOfParsableVariable.EMPTY_LIST;
        for(PositionedString expr : originalSkolemDeclarations) {
            ListOfLogicVariable translated 
                = translator.translateVariableDeclaration(expr);
            for(LogicVariable lv : translated) {
                freeVars = freeVars.prepend(lv);
            }
        }
        
        //translate predicates
        SetOfTerm predicates = SetAsListOfTerm.EMPTY_SET;
        for(PositionedString ps : originalPredicates) {
            String[] exprs = ps.text.split(",", 0);
            
            for(int i = 0; i < exprs.length; i++) {
                FormulaWithAxioms translated
                    = translator.translateExpression(
                            new PositionedString(exprs[i]), 
                            programMethod.getContainerType(),
                            selfVar, 
                            paramVars.append(freeVars), 
                            null, 
                            null,
                            atPreFunctions);
                assert translated.getAxioms().isEmpty();
                predicates = predicates.add(translated.getFormula());                
            }
        }
        
        //translate assignable
        SetOfLocationDescriptor assignable;
        if(originalAssignable.isEmpty()) {
            assignable = EverythingLocationDescriptor.INSTANCE_AS_SET;
        } else {
            assignable = SetAsListOfLocationDescriptor.EMPTY_SET;
            for(PositionedString expr : originalAssignable) {
                SetOfLocationDescriptor translated 
                    = translator.translateAssignableExpression(
                                        expr, 
                                        programMethod.getContainerType(),
                                        selfVar, 
                                        paramVars);
                assignable = assignable.union(translated);        
            }
        }
        
        //translate variant
        Term variant;
        if(originalVariant == null) {
            variant = null;
        } else {
            FormulaWithAxioms translated 
                = translator.translateExpression(
                                        originalVariant,
                                        programMethod.getContainerType(),
                                        selfVar,
                                        paramVars,
                                        null,
                                        null,
                                        atPreFunctions);
            assert translated.getAxioms().isEmpty();
            variant = translated.getFormula();
        }
        
        //create loop invariant annotation
        Term selfTerm = selfVar == null ? null : TB.var(selfVar);
        return new LoopInvariantImpl(loop,
                                     invariant,
                                     predicates,
                                     assignable,
                                     variant,
                                     selfTerm,
                                     atPreFunctions,
                                     true);
    }
    
    
    public LoopInvariant createJMLLoopInvariant(
                                        ProgramMethod programMethod,
                                        LoopStatement loop,
                                        TextualJMLLoopSpec textualLoopSpec) 
            throws SLTranslationException {
        return createJMLLoopInvariant(programMethod,
                                      loop,
                                      textualLoopSpec.getInvariant(),
                                      textualLoopSpec.getSkolemDeclarations(),
                                      textualLoopSpec.getPredicates(),
                                      textualLoopSpec.getAssignable(),
                                      textualLoopSpec.getVariant());
    }
}
