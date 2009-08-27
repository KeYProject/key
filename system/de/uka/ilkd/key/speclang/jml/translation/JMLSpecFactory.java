// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
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
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final Services services;
    private final JMLTranslator translator;
    
    private int invCounter;
    
    
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
    
    
    private String getContractName(ProgramMethod programMethod, 
	                           Behavior behavior) {
        return "JML " + behavior.toString() + "contract";
    }
    
    
    /**
     * Collects local variables of the passed statement that are visible for 
     * the passed loop. Returns null if the loop has not been found.
     */
    private ImmutableList<ProgramVariable> collectLocalVariables(
	    					StatementContainer sc, 
                                                LoopStatement loop){
        ImmutableList<ProgramVariable> result 
        	= ImmutableSLList.<ProgramVariable>nil();
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
                ImmutableList< ProgramVariable > lpv 
                    = collectLocalVariables((StatementContainer) s, loop);
                if(lpv != null){ 
                    result = result.prepend(lpv);
                    return result;
                }
            } else if(s instanceof BranchStatement) {
                BranchStatement bs = (BranchStatement) s;
                for(int j = 0, n = bs.getBranchCount(); j < n; j++) {
                    ImmutableList< ProgramVariable > lpv 
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
     */
    private ImmutableSet<OperationContract> createJMLOperationContracts(
                                ProgramMethod pm,
                                Behavior originalBehavior,                              
                                PositionedString customName,
                                ImmutableList<PositionedString> originalRequires,
                                ImmutableList<PositionedString> originalAssignable,
                                ImmutableList<PositionedString> originalEnsures,
                                ImmutableList<PositionedString> originalSignals,
                                ImmutableList<PositionedString> originalSignalsOnly,
                                ImmutableList<PositionedString> originalDiverges) 
            throws SLTranslationException {
        assert pm != null;
        assert originalBehavior != null;
        assert originalRequires != null;
        assert originalAssignable != null;
        assert originalEnsures != null;
        assert originalSignals != null;
        assert originalSignalsOnly != null;
        assert originalDiverges != null;

        //create variables for self, parameters, result, exception,
        //and the map for atPre-Functions
        ProgramVariable selfVar = TB.selfVar(services, pm, false);
        ImmutableList<ProgramVariable> paramVars 
        	= TB.paramVars(services, pm, false);
        ProgramVariable resultVar = TB.resultVar(services, pm, false);
        ProgramVariable excVar = TB.excVar(services, pm, false);
        Term heapAtPre = TB.var(TB.heapAtPreVar(services, "heapAtPre", false));

        //translate requires
        Term requires = TB.tt();
        for(PositionedString expr : originalRequires) {
            Term translated 
                = translator.translateExpression(
                    expr,
                    pm.getContainerType(),
                    selfVar, 
                    paramVars, 
                    null, 
                    null,
                    null);
            requires = TB.and(requires, translated);        
        }

        //translate assignable
        Term assignable;
        if(originalAssignable.isEmpty()) {
            assignable = TB.allLocs(services);
        } else {
            assignable = TB.empty(services);
            for(PositionedString expr : originalAssignable) {
        	Term translated 
        		= translator.translateAssignableExpression(
        				expr, 
        				pm.getContainerType(),
        				selfVar, 
        				paramVars);
        	assignable = TB.union(services, assignable, translated);
            }
            assignable = TB.union(services, 
        	                  assignable, 
        	                  TB.freshLocs(services, TB.heap(services)));
        }

        //translate ensures
        Term ensures = TB.tt();
        for(PositionedString expr : originalEnsures) {
            Term translated 
                = translator.translateExpression(
                    expr,
                    pm.getContainerType(),
                    selfVar, 
                    paramVars, 
                    resultVar, 
                    excVar,
                    heapAtPre);
            ensures = TB.and(ensures, translated);        
        }

        //translate signals
        Term signals = TB.tt();
        for(PositionedString expr : originalSignals) {
            Term translated 
                = translator.translateSignalsExpression(
                    expr, 
                    pm.getContainerType(),
                    selfVar, 
                    paramVars, 
                    resultVar, 
                    excVar,
                    heapAtPre);
            signals = TB.and(signals, translated);        
        }

        //translate signals_only
        Term signalsOnly = TB.tt();
        for(PositionedString expr : originalSignalsOnly) {
            Term translated 
                = translator.translateSignalsOnlyExpression(
                    expr,
                    pm.getContainerType(),
                    excVar);
            signalsOnly = TB.and(signalsOnly, translated);
        }

        //translate diverges
        Term diverges = TB.tt();
        for(PositionedString expr : originalDiverges) {
            Term translated 
                = translator.translateExpression(
                    expr, 
                    pm.getContainerType(),
                    selfVar, 
                    paramVars, 
                    null, 
                    null,
                    null);
            diverges = TB.and(diverges, translated);        
        }

        //translate normal_behavior / exceptional_behavior
        if(originalBehavior == Behavior.NORMAL_BEHAVIOR) {
            assert originalSignals.isEmpty();
            assert originalSignalsOnly.isEmpty();
            signals = TB.ff();
            signalsOnly = TB.ff();
        } else if(originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR) {
            assert originalEnsures.isEmpty();
            ensures = TB.ff();
        }

        //create contract(s)
        ImmutableSet<OperationContract> result 
            = DefaultImmutableSet.<OperationContract>nil();
        Term excNull = TB.equals(TB.var(excVar), TB.NULL(services));
        Term post1 
            = (originalBehavior == Behavior.NORMAL_BEHAVIOR
               ? ensures
               : TB.imp(excNull, ensures));
        Term post2 
            = (originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR
               ? TB.and(signals, signalsOnly)
               : TB.imp(TB.not(excNull), TB.and(signals, signalsOnly)));
        Term post = TB.and(post1, post2);
        String name = (customName.text.length() > 0 
                       ? customName.text 
                       : getContractName(pm, originalBehavior));
        
        if(diverges.equals(TB.ff())) {
            OperationContract contract
                = new OperationContractImpl(name,
                                            pm,
                                            Modality.DIA,
                                            requires,
                                            post,
                                            assignable,
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            heapAtPre); 
            result = result.add(contract);
        } else if(diverges.equals(TB.tt())) {
            OperationContract contract
                = new OperationContractImpl(name,
                                            pm,
                                            Modality.BOX,
                                            requires,
                                            post,
                                            assignable,
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            heapAtPre); 
            result = result.add(contract);
        } else {
            OperationContract contract1
                = new OperationContractImpl(name,
                                            pm,
                                            Modality.DIA,
                                            TB.and(requires, TB.not(diverges)),
                                            post,
                                            assignable,
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            heapAtPre);
            OperationContract contract2
                = new OperationContractImpl(name,
                                            pm,
                                            Modality.BOX,
                                            requires,
                                            post,
                                            assignable,
                                            selfVar,
                                            paramVars,
                                            resultVar,
                                            excVar,
                                            heapAtPre);
            result = result.add(contract1).add(contract2);
        }

        return result;
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
        ProgramVariable selfVar 
        	= new LocationVariable(new ProgramElementName("self"), kjt);
        
        //translate expression
        Term inv = translator.translateExpression(originalInv,
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
    
    
    public ImmutableSet<OperationContract> createJMLOperationContracts(
            				ProgramMethod pm,
            				TextualJMLSpecCase textualSpecCase) 
            throws SLTranslationException {
        return createJMLOperationContracts(
                                    pm,
                                    textualSpecCase.getBehavior(),
                                    textualSpecCase.getName(),
                                    textualSpecCase.getRequires(),
                                    textualSpecCase.getAssignable(),
                                    textualSpecCase.getEnsures(),
                                    textualSpecCase.getSignals(),
                                    textualSpecCase.getSignalsOnly(),
                                    textualSpecCase.getDiverges());
    }     
    
    
    public LoopInvariant createJMLLoopInvariant(
                            ProgramMethod pm,
                            LoopStatement loop,
                            ImmutableList<PositionedString> originalInvariant,
                            ImmutableList<PositionedString> originalSkolemDeclarations,
                            ImmutableList<PositionedString> originalPredicates,
                            ImmutableList<PositionedString> originalAssignable,
                            PositionedString originalVariant) 
            throws SLTranslationException {                
        assert pm != null;
        assert loop != null;
        assert originalInvariant != null;
        assert originalSkolemDeclarations != null;
        assert originalPredicates != null;
        assert originalAssignable != null;
        
        //create variables for self, parameters, other relevant local variables 
        //(disguised as parameters to the translator) and the map for 
        //atPre-Functions
        ProgramVariable selfVar = TB.selfVar(services, pm, false);
        ImmutableList<ProgramVariable> paramVars 
        	= ImmutableSLList.<ProgramVariable>nil();
        int numParams = pm.getParameterDeclarationCount();
        for(int i = numParams - 1; i >= 0; i--) {
            ParameterDeclaration pd = pm.getParameterDeclarationAt(i);
            paramVars = paramVars.prepend((ProgramVariable) 
                                          pd.getVariableSpecification()
                                             .getProgramVariable());
        }

        ImmutableList<ProgramVariable> localVars 
            = collectLocalVariables(pm.getBody(), loop);        
        paramVars = paramVars.append(localVars);
        Term heapAtPre = TB.var(TB.heapAtPreVar(services, "heapAtPre", false));
        
        //translate invariant
        Term invariant;
        if(originalInvariant.isEmpty()) {
            invariant = null;
        } else {
            invariant = TB.tt();
            for(PositionedString expr : originalInvariant) {
                Term translated 
                    = translator.translateExpression(
                                            expr, 
                                            pm.getContainerType(),
                                            selfVar, 
                                            paramVars, 
                                            null, 
                                            null,
                                            heapAtPre);
                invariant = TB.and(invariant, translated);
            }
        }

        
        //translate skolem declarations
        ImmutableList<ProgramVariable> freeVars = ImmutableSLList.<ProgramVariable>nil();
        for(PositionedString expr : originalSkolemDeclarations) {
            ImmutableList<ProgramVariable> translated 
                = translator.translateVariableDeclaration(expr);
            for(ProgramVariable pv : translated) {
                freeVars = freeVars.prepend(pv);
            }
        }
        
        //translate predicates
        ImmutableSet<Term> predicates = DefaultImmutableSet.<Term>nil();
        for(PositionedString ps : originalPredicates) {
            String[] exprs = ps.text.split(",", 0);
            
            for(int i = 0; i < exprs.length; i++) {
                Term translated
                    = translator.translateExpression(
                            new PositionedString(exprs[i]), 
                            pm.getContainerType(),
                            selfVar, 
                            paramVars.append(freeVars), 
                            null, 
                            null,
                            heapAtPre);
                predicates = predicates.add(translated);                
            }
        }
        
        //translate assignable
        Term assignable;
        if(originalAssignable.isEmpty()) {
            assignable = TB.allLocs(services);
        } else {
            assignable = TB.empty(services);
            for(PositionedString expr : originalAssignable) {
        	Term translated 
        	    = translator.translateAssignableExpression(
        		    expr, 
        		    pm.getContainerType(),
        		    selfVar, 
        		    paramVars);
        	assignable = TB.union(services, assignable, translated);        
            }
            assignable = TB.union(services,
        	                  assignable, 
        	                  TB.freshLocs(services, TB.heap(services)));
        }
        
        //translate variant
        Term variant;
        if(originalVariant == null) {
            variant = null;
        } else {
            Term translated 
                = translator.translateExpression(
                                        originalVariant,
                                        pm.getContainerType(),
                                        selfVar,
                                        paramVars,
                                        null,
                                        null,
                                        heapAtPre);
            variant = translated;
        }
        
        //create loop invariant annotation
        Term selfTerm = selfVar == null ? null : TB.var(selfVar);
        return new LoopInvariantImpl(loop,
                                     invariant,
                                     predicates,
                                     assignable,
                                     variant,
                                     selfTerm,
                                     heapAtPre,
                                     true);
    }
    
    
    public LoopInvariant createJMLLoopInvariant(
                                        ProgramMethod pm,
                                        LoopStatement loop,
                                        TextualJMLLoopSpec textualLoopSpec) 
            throws SLTranslationException {
        return createJMLLoopInvariant(pm,
                                      loop,
                                      textualLoopSpec.getInvariant(),
                                      textualLoopSpec.getSkolemDeclarations(),
                                      textualLoopSpec.getPredicates(),
                                      textualLoopSpec.getAssignable(),
                                      textualLoopSpec.getVariant());
    }
}
