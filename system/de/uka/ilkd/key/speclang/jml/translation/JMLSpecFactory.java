// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml.translation;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rtsj.java.RTSJInfo;
import de.uka.ilkd.key.rtsj.proof.init.RTSJProfile;
import de.uka.ilkd.key.speclang.*;
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
    
    
    private ImmutableSet<ProgramMethod> getOverridingMethods(ProgramMethod pm) {
        JavaInfo ji = services.getJavaInfo();
        String name   = pm.getMethodDeclaration().getName();
        int numParams = pm.getParameterDeclarationCount();
        ImmutableSet<ProgramMethod> result = DefaultImmutableSet.<ProgramMethod>nil();
        
        KeYJavaType kjt = pm.getContainerType();
        assert kjt != null;
        for(KeYJavaType sub : ji.getAllSubtypes(kjt)) {
            assert sub != null;
            
            ImmutableList<ProgramMethod> subPms 
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
    private ImmutableList<ParsableVariable> collectLocalVariables(StatementContainer sc, 
                                                         LoopStatement loop){
        ImmutableList<ParsableVariable> result = ImmutableSLList.<ParsableVariable>nil();
        for(int i = 0, m = sc.getStatementCount(); i < m; i++) {
            Statement s = sc.getStatementAt(i);
            
            if(s instanceof For) {
        	ImmutableArray<VariableSpecification> avs 
        		= ((For)s).getVariablesInScope();
        	for(int j = 0, n = avs.size(); j < n; j++) {
        	    VariableSpecification vs = avs.get(j);
        	    ProgramVariable pv 
        	    	= (ProgramVariable) vs.getProgramVariable();
        	    result = result.prepend(pv);
        	}
            }

            if(s == loop) {
                return result;
            } else if(s instanceof LocalVariableDeclaration) {
                ImmutableArray<VariableSpecification> vars = 
                    ((LocalVariableDeclaration) s).getVariables();
                for(int j = 0, n = vars.size(); j < n; j++) {
                    ProgramVariable pv 
                        = (ProgramVariable) vars.get(j).getProgramVariable();
                    result = result.prepend(pv);
                }
            } else if(s instanceof StatementContainer) {
                ImmutableList<ParsableVariable> lpv 
                    = collectLocalVariables((StatementContainer) s, loop);
                if(lpv != null){ 
                    result = result.prepend(lpv);
                    return result;
                }
            } else if(s instanceof BranchStatement) {
                BranchStatement bs = (BranchStatement) s;
                for(int j = 0, n = bs.getBranchCount(); j < n; j++) {
                    ImmutableList<ParsableVariable> lpv 
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
    
    
    /**
     * Creates operation contracts out of the passed JML specification.
     * @param paramVars variables to be used as parameters in the 
     * translation. If null, appropriate variables are created out of the 
     * signature information for the programMethod. 
     */
    private ImmutableSet<OperationContract> createJMLOperationContracts(
                                ProgramMethod programMethod,
                                Behavior originalBehavior,                              
                                PositionedString customName,
                                ImmutableList<PositionedString> originalRequires,
                                ImmutableList<PositionedString> originalAssignable,
                                ImmutableList<PositionedString> originalEnsures,
                                ImmutableList<PositionedString> originalSignals,
                                ImmutableList<PositionedString> originalSignalsOnly,
                                ImmutableList<PositionedString> originalDiverges,                               
                                PositionedString originalWorkingSpace,
                                ImmutableList<ParsableVariable> paramVars) 
            throws SLTranslationException {
        assert programMethod != null;
        assert originalBehavior != null;
        assert originalRequires != null;
        assert originalAssignable != null;
        assert originalEnsures != null;
        assert originalSignals != null;
        assert originalSignalsOnly != null;
        assert originalDiverges != null;

        //create variables for self, parameters, result, exception,
        //and the map for atPre-Functions
        ParsableVariable selfVar = SVF.createSelfVar(services, 
                                                     programMethod, 
                                                     false);
        if(paramVars == null) {
            paramVars = SVF.createParamVars(services, programMethod, false);
        }
        ParsableVariable resultVar = SVF.createResultVar(services, 
                                                         programMethod, 
                                                         false);
        ParsableVariable excVar = SVF.createExcVar(services,
                                                   programMethod, 
                                                   false);
        Map<Operator, Function> atPreFunctions 
            = new LinkedHashMap<Operator, Function>();

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
        
        //translate working_space
        if(originalWorkingSpace==null){
            originalWorkingSpace = new PositionedString("0;");
        }
        Term workingSpace = null;
        Term imCons=null;
        FormulaWithAxioms wsPost = new FormulaWithAxioms(TB.tt());
        if((ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile) && 
        		((RTSJProfile) ProofSettings.DEFAULT_SETTINGS.getProfile()).memoryConsumption()) {
	        ProgramVariable initialMemoryArea = ((RTSJInfo) services.getJavaInfo()).
	        getDefaultMemoryArea();
	        Term imTerm = TB.var(initialMemoryArea);
	        imCons = TB.dot(imTerm, services.getJavaInfo().getAttribute(
	        "consumed", "javax.realtime.MemoryArea"));
	        String ws = originalWorkingSpace.text.trim();
	        Term oldCons = translator.translateExpression(
	                new PositionedString("\\old(\\currentMemoryArea.consumed)",
	                        originalWorkingSpace.fileName,
	                        new Position(originalWorkingSpace.pos.getLine(), 
	                                originalWorkingSpace.pos.getColumn())),
	                                programMethod.getContainerType(),
	                                selfVar, 
	                                paramVars, 
	                                resultVar, 
	                                excVar,
	                                atPreFunctions).getFormula();
	        Term oldWS = translator.translateExpression(
	                new PositionedString("\\old("+ws.substring(0, ws.length()-1)+")",
	                        originalWorkingSpace.fileName,
	                        new Position(originalWorkingSpace.pos.getLine(), 
	                                originalWorkingSpace.pos.getColumn()-5)),
	                                programMethod.getContainerType(),
	                                selfVar, 
	                                paramVars, 
	                                resultVar, 
	                                excVar,
	                                atPreFunctions).getFormula();
	        Function add = (Function) services.getNamespaces().functions().lookup(new Name("add"));
	        Function leq = (Function) services.getNamespaces().functions().lookup(new Name("leq"));
	        wsPost = new FormulaWithAxioms(TB.func(leq, imCons, TB.func(add, oldCons, oldWS)));
               
    	}    
	        
        workingSpace = translator.translateExpression(
                originalWorkingSpace,
                programMethod.getContainerType(),
                selfVar, 
                paramVars, 
                resultVar, 
                excVar,
                atPreFunctions).getFormula();        
        
        //translate assignable
        ImmutableSet<LocationDescriptor> assignable;
        if(originalAssignable.isEmpty()) {
            assignable = EverythingLocationDescriptor.INSTANCE_AS_SET;
        } else {
            assignable = DefaultImmutableSet.<LocationDescriptor>nil();
            for(PositionedString expr : originalAssignable) {
                ImmutableSet<LocationDescriptor> translated 
                    = translator.translateAssignableExpression(
                        expr, 
                        programMethod.getContainerType(),
                        selfVar, 
                        paramVars);
                assignable = assignable.union(translated);        
            }
            if(assignable.size()!=0 && ((ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile) && 
            		((RTSJProfile) ProofSettings.DEFAULT_SETTINGS.getProfile()).memoryConsumption())){
                assignable = assignable.add(new BasicLocationDescriptor(imCons));
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
        ImmutableSet<OperationContract> result 
            = DefaultImmutableSet.<OperationContract>nil();
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
        FormulaWithAxioms post = post1.conjoin(post2);
        String name = getContractName(originalBehavior);        
        String displayName = (customName.text.length() > 0 
                              ? customName.text + " [" + name + "]" 
                              : name); 
        
        if(diverges.equals(FormulaWithAxioms.FF)) {
            OperationContract contract
                = new OperationContractImpl(name,
                                            displayName,
                                            programMethod,
                                            Modality.DIA,
                                            requires,
                                            post,
                                            wsPost,
                                            assignable,
                                            workingSpace,                                            
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            atPreFunctions); 
            result = result.add(contract);
        } else if(diverges.equals(FormulaWithAxioms.TT)) {
            OperationContract contract
                = new OperationContractImpl(name,
                                            displayName,
                                            programMethod,
                                            Modality.BOX,
                                            requires,
                                            post,
                                            wsPost,
                                            assignable,
                                            workingSpace,                                            
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            atPreFunctions); 
            result = result.add(contract);
        } else {
            String name2 = getContractName(originalBehavior);
            String displayName2 = (customName.text.length() > 0 
                                   ? customName.text + "[" + name2 + "]" 
                                   : name2);
            OperationContract contract1
                = new OperationContractImpl(name,
                                            displayName,
                                            programMethod,
                                            Modality.DIA,
                                            requires.conjoin(diverges.negate()),
                                            post,
                                            wsPost,
                                            assignable,
                                            workingSpace,                                           
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            atPreFunctions);
            OperationContract contract2
                = new OperationContractImpl(name2,
                                            displayName2,
                                            programMethod,
                                            Modality.BOX,
                                            requires,
                                            post,
                                            wsPost,
                                            assignable,
                                            workingSpace,                                           
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            atPreFunctions);
            result = result.add(contract1).add(contract2);
        }

        return result;
    }
    
    
    private ImmutableSet<OperationContract> createJMLOperationContracts(
            ProgramMethod programMethod,
            TextualJMLSpecCase textualSpecCase,
            ImmutableList<ParsableVariable> paramVars) 
            throws SLTranslationException {
        return createJMLOperationContracts(
                                    programMethod,
                                    textualSpecCase.getBehavior(),
                                    textualSpecCase.getName(),
                                    textualSpecCase.getRequires(),
                                    textualSpecCase.getAssignable(),
                                    textualSpecCase.getEnsures(),
                                    textualSpecCase.getSignals(),
                                    textualSpecCase.getSignalsOnly(),
                                    textualSpecCase.getDiverges(),
                                    textualSpecCase.getWorkingSpace(),                                    
                                    paramVars);
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
        FormulaWithAxioms inv;
        try{
            inv = translator.translateExpression(originalInv,
        	    				 kjt,
                                                 selfVar,
                                                 null,
                                                 null,
                                                 null,
                                                 null);        
        } catch (SLTranslationException sle) {
            throw sle;
        } catch (Exception e) {                   
            throw new SLTranslationException("Unexpected error when translating invariant of class " 
        	    + kjt.getFullName() + "\nInvariant to parse: " + originalInv  + "\nError:" + e, originalInv.fileName, 
        	    originalInv.pos);
        }
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
    
    
    public ImmutableSet<OperationContract> createJMLOperationContracts(
                                ProgramMethod programMethod,
                                Behavior originalBehavior,				
				PositionedString customName,
                                ImmutableList<PositionedString> originalRequires,
                                ImmutableList<PositionedString> originalAssignable,
                                ImmutableList<PositionedString> originalEnsures,
                                ImmutableList<PositionedString> originalSignals,
                                ImmutableList<PositionedString> originalSignalsOnly,
                                ImmutableList<PositionedString> originalDiverges) 
            throws SLTranslationException {
        return createJMLOperationContracts(programMethod,
                                           originalBehavior,
                                           customName,
                                           originalRequires,
                                           originalAssignable,
                                           originalEnsures,
                                           originalSignals,
                                           originalSignalsOnly,
                                           originalDiverges,					   
                                           null,
                                           null);
    }
    
    
    public ImmutableSet<OperationContract> createJMLOperationContracts(
                                        ProgramMethod programMethod,
                                        TextualJMLSpecCase textualSpecCase) 
            throws SLTranslationException {
        return createJMLOperationContracts(programMethod, 
                                           textualSpecCase, 
                                           null);
    }
    
    
    public ImmutableSet<OperationContract> createJMLOperationContractsAndInherit(
                                        ProgramMethod programMethod,
                                        TextualJMLSpecCase textualSpecCase) 
            throws SLTranslationException {
        //parameter names of original method must be used for all inherited 
        //instances of the contract
        ImmutableList<ParsableVariable> paramVars 
            = SVF.createParamVars(services, programMethod, false);
        
        //create contracts for original method
        ImmutableSet<OperationContract> result 
            = createJMLOperationContracts(programMethod, 
                                          textualSpecCase, 
                                          paramVars);
        
        //create contracts for all overriding methods
        for(ProgramMethod subPm : getOverridingMethods(programMethod)) {
            
            
            ImmutableSet<OperationContract> subContracts 
                = createJMLOperationContracts(subPm, 
                                              textualSpecCase, 
                                              paramVars);
            result = result.union(subContracts);
        }
        
        return result;
    }
    
    
    public LoopInvariant createJMLLoopInvariant(
                            ProgramMethod programMethod,
                            LoopStatement loop,
                            ImmutableList<PositionedString> originalInvariant,
                            ImmutableList<PositionedString> originalSkolemDeclarations,
                            ImmutableList<PositionedString> originalPredicates,
                            ImmutableList<PositionedString> originalAssignable,
	PositionedString originalVariant,
	ImmutableList<PositionedString> originalParametrizedWorkingspace,
                            PositionedString originalWorkingSpaceLocal,
                            PositionedString originalWorkingSpaceConstructed,
                            PositionedString originalWorkingSpaceReentrant) 
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
        ImmutableList<ParsableVariable> paramVars = ImmutableSLList.<ParsableVariable>nil();
        int numParams = programMethod.getParameterDeclarationCount();
        for(int i = numParams - 1; i >= 0; i--) {
            ParameterDeclaration pd = programMethod.getParameterDeclarationAt(i);
            paramVars = paramVars.prepend((ProgramVariable) 
                                          pd.getVariableSpecification()
                                             .getProgramVariable());
        }

        ImmutableList<ParsableVariable> localVars 
            = collectLocalVariables(programMethod.getBody(), loop);        
        paramVars = paramVars.append(localVars);
        Map<Operator, Function> atPreFunctions = new LinkedHashMap<Operator, Function>();
        
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
            invariant = TB.and(invariant, TB.inReachableState(services));
        }

        
        Term parametrizedWS = TB.tt();
        for(PositionedString expr : originalParametrizedWorkingspace) {
            String s = expr.toString();
            String param = s.substring(s.indexOf("{")+1, s.indexOf("}"));
            String ws = s.substring(s.indexOf("}")+1);
            // HACK
            ws = param.trim() +".consumed  <"+ ws;
            FormulaWithAxioms translatedWS
            = translator.translateExpression(
                                    new PositionedString(ws, expr.fileName, expr.pos), 
                                    programMethod.getContainerType(),
                                    selfVar, 
                                    paramVars, 
                                    null, 
                                    null,
                                    atPreFunctions);
            assert translatedWS.getAxioms().isEmpty();
            parametrizedWS = TB.and(translatedWS.getFormula(), parametrizedWS);
        }
        
        //translate skolem declarations
        ImmutableList<ParsableVariable> freeVars = ImmutableSLList.<ParsableVariable>nil();
        for(PositionedString expr : originalSkolemDeclarations) {
            ImmutableList<LogicVariable> translated 
                = translator.translateVariableDeclaration(expr);
            for(LogicVariable lv : translated) {
                freeVars = freeVars.prepend(lv);
            }
        }
        
        //translate predicates
        ImmutableSet<Term> predicates = DefaultImmutableSet.<Term>nil();
        for(PositionedString ps : originalPredicates) {
            String[] exprs = ps.text.split(",", 0);

            for (String expr : exprs) {
                FormulaWithAxioms translated
                        = translator.translateExpression(
                        new PositionedString(expr),
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
        
        Term workingSpaceLocal = null;
        if(originalWorkingSpaceLocal == null)
            originalWorkingSpaceLocal = new PositionedString("0;");
        FormulaWithAxioms translated = translator.translateExpression(
                originalWorkingSpaceLocal,
                programMethod.getContainerType(),
                selfVar,
                paramVars,
                null,
                null,
                atPreFunctions);
        assert translated.getAxioms().isEmpty();
        workingSpaceLocal = translated.getFormula(); 
                
        Term workingSpaceConstructed = null;
        if(originalWorkingSpaceConstructed == null)
            originalWorkingSpaceConstructed = new PositionedString("0;");
        translated = translator.translateExpression(
                originalWorkingSpaceConstructed,
                programMethod.getContainerType(),
                selfVar,
                paramVars,
                null,
                null,
                atPreFunctions);
        workingSpaceConstructed = translated.getFormula(); 
        
        Term workingSpaceReentrant = null;
        if(originalWorkingSpaceReentrant == null)
            originalWorkingSpaceReentrant = new PositionedString("0;");
        translated = translator.translateExpression(
                originalWorkingSpaceReentrant,
                programMethod.getContainerType(),
                selfVar,
                paramVars,
                null,
                null,
                atPreFunctions);
        workingSpaceReentrant = translated.getFormula(); 
                
        /*        Term imCons=null;
        ProgramVariable initialMemoryArea = services.getJavaInfo().
        getDefaultMemoryArea();
        Term imTerm = TB.var(initialMemoryArea);
        imCons = TB.dot(imTerm, services.getJavaInfo().getAttribute(
                "consumed", "javax.realtime.MemoryArea"));*/
        ImmutableSet<LocationDescriptor> assignable;
        if(originalAssignable.isEmpty()) {
            assignable = EverythingLocationDescriptor.INSTANCE_AS_SET;
        } else {
            assignable = DefaultImmutableSet.<LocationDescriptor>nil();
            for(PositionedString expr : originalAssignable) {
                ImmutableSet<LocationDescriptor> translatedL 
                    = translator.translateAssignableExpression(
                                        expr, 
                                        programMethod.getContainerType(),
                                        selfVar, 
                                        paramVars);
                assignable = assignable.union(translatedL);        
            }
//            if(imCons!=null) assignable = assignable.add(new BasicLocationDescriptor(imCons));
        }
        
        //translate variant
        Term variant;
        if(originalVariant == null) {
            variant = null;
        } else {
            translated 
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
                                     new LoopPredicateSet(predicates),
                                     new LocationDescriptorSet(assignable),
                                     variant,
                                     parametrizedWS,
                                     workingSpaceLocal,
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
                                      textualLoopSpec.getVariant(),
                                      textualLoopSpec.getParametrizedWorkingspace(),
                                      textualLoopSpec.getWorkingSpaceLocal(),
                                      textualLoopSpec.getWorkingSpaceConstructed(),
                                      textualLoopSpec.getWorkingSpaceReentrant());
    }
}
