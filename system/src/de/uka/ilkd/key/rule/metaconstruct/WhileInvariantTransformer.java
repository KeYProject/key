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

package de.uka.ilkd.key.rule.metaconstruct;


import java.util.ArrayList;
import java.util.LinkedList;
import java.util.ListIterator;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class WhileInvariantTransformer {
    /** the outer label that is used to leave the while loop ('l1') */
    private final SchemaVariable outerLabel = 
        SchemaVariableFactory.createProgramSV(new ProgramElementName("outer_label"),
                                       ProgramSVSort.LABEL, false);
    /** the inner label ('l2') */
    private final SchemaVariable innerLabel =
        SchemaVariableFactory.createProgramSV(new ProgramElementName("inner_label"),
                                       ProgramSVSort.LABEL, false);
    /** list of the labels */
    private ImmutableList<SchemaVariable> instantiations  = null;

    /** list of breaks that lead to abrupt termination
     * of the loop to be transformed. Is initialised by
     * the method neededInstantiations that is invoked 
     * before calculate
     */
    private LinkedList<BreakToBeReplaced> breakList;

    /** The JavaInfo object which is handed over as
     * a parameter of calculate.
     */
    private JavaInfo javaInfo;
    private TypeConverter typeConv;
    private TermFactory tf;

    private ProgramElement body;
    private Term inv, post;
    private JavaNonTerminalProgramElement root; 
    private Modality modality;
    
    private KeYJavaType returnType;
    
    public WhileInvariantTransformer() {
    }

   
    /**
     * initialises this meta operator
     * @param term the instantiated Term passed to the TermTransformer 
     * @param services the Services providing access to signature and
     * type model
     */
    private void init(Term initialPost, Term invariantFramingTermination, Services services) {
        root = (JavaNonTerminalProgramElement)
              initialPost.javaBlock().program();  
        modality = (Modality)initialPost.op();
        
        ReplaceWhileLoop removeWhile = 
            new ReplaceWhileLoop(root, null, services);
        removeWhile.start();       
        
        body = removeWhile.getTheLoop();
        
        // some initialisations...
                
        inv = invariantFramingTermination;
        post = initialPost.sub(0);

        javaInfo = services.getJavaInfo();
        tf = services.getTermFactory() ;
        typeConv = services.getTypeConverter();
        
        returnType = removeWhile.returnType();
    }
    
    
    /** calculates the resulting term. */
    public Term transform(WhileInvariantRule rule, Goal goal, Sequent applicationSequent, PosInOccurrence applicationPos, Term initialPost, Term invariantFramingTermination, SVInstantiations svInst, Services services) {
        
        // global initialisation
        init(initialPost, invariantFramingTermination, services);
        
        // local initialisation
        ArrayList<ProgramElement> stmnt = new ArrayList<ProgramElement>();
        ArrayList<If> breakIfCascade = new ArrayList<If>();
        
        
        ProgramVariable contFlag   = getNewLocalvariable("cont", "boolean", services);
        ProgramVariable returnFlag = getNewLocalvariable("rtrn", "boolean", services);
        ProgramVariable breakFlag  = getNewLocalvariable("brk", "boolean", services);                   
        // xxx how to ensure that "exc" has not been used before??
        ProgramVariable excFlag    = getNewLocalvariable("exc", "boolean", services);        
        ProgramVariable excParam   = getNewLocalvariable("e", "java.lang.Throwable", services);          
        ProgramVariable thrownException = 
            getNewLocalvariable("thrownExc", "java.lang.Throwable", services);
        
        ProgramVariable returnExpression = null;
        if (returnType != null) {
            returnExpression = getNewLocalvariable("returnExpr", returnType, services);
        }
        
        Term contFlagTerm   = null;
        Term returnFlagTerm = null;
        Term breakFlagTerm  = null;
        Term excFlagTerm    = null;
        
        // end of initialisation............
        
        int breakCounter = 0;
        final ListIterator<BreakToBeReplaced> it = breakList.listIterator(0);
        int numberOfBreaks = 0;
        while (it.hasNext()) {
            BreakToBeReplaced b = it.next();
            ProgramVariable newVar = getNewLocalvariable("break_"+breakCounter++, 
                                                         "boolean", services);
            b.setProgramVariable(newVar);
            stmnt.add(KeYJavaASTFactory.declare
                      (newVar, BooleanLiteral.FALSE,
                       javaInfo.getKeYJavaType("boolean")));
            numberOfBreaks++;
            Statement s;
            if (b.getBreak().getLabel() != null) 
                s = KeYJavaASTFactory.breakStatement(b.getBreak().getLabel());
            else 
                s = KeYJavaASTFactory.emptyStatement();
            breakIfCascade.add(KeYJavaASTFactory.ifThen(newVar, s));
        }
        
        WhileInvariantTransformation w = 
            new WhileInvariantTransformation(body,
                                             (ProgramElementName)
                                             svInst.getInstantiation(outerLabel),
                                             (ProgramElementName)
                                             svInst.getInstantiation(innerLabel),
                                             contFlag, excFlag, excParam, 
                                             thrownException, breakFlag, 
                                             returnFlag, returnExpression,
                                             breakList, services);
        w.start();
        
        ArrayList<Term> resultSubterms = new ArrayList<Term>();
        
        // normal case and continue
        if (w.continueOccurred()) {
            stmnt.add(contFlagDecl(contFlag));
            contFlagTerm =  services.getTermBuilder().equals(typeConv.convertToLogicElement(contFlag), 
        	    	             typeConv.getBooleanLDT().getTrueTerm());
        }
        
        // exception case
        resultSubterms.add(throwCase(excFlag, 
                                     thrownException, 
                                     post,
                                     rule,
                                     goal,
                                     applicationPos,
                                     services));
        
        // return case
        if (w.returnOccurred()) {
            stmnt.add(returnFlagDecl(returnFlag, svInst));
            returnFlagTerm = 
                typeConv.convertToLogicElement(returnFlag);
            resultSubterms.add
            (returnCase(returnFlag, returnType,
                        returnExpression, post, rule, goal, applicationPos, services));
            
            if (returnType != null) {
                stmnt.add(KeYJavaASTFactory.declare
                          (returnExpression, returnType));
            }
        }
        
        
        // break case
        if (numberOfBreaks > 0) {
            stmnt.add(breakFlagDecl(breakFlag));
            breakFlagTerm = 
                typeConv.convertToLogicElement(breakFlag);
            resultSubterms.add(breakCase(breakFlag, post, 
                                         breakIfCascade,
                                         rule,
                                         goal,
                                         applicationPos,
                                         services)); 
        }
        
        
        // we catch all exceptions
        stmnt.add(KeYJavaASTFactory.declare
                  (excFlag, BooleanLiteral.FALSE,
                   javaInfo.getKeYJavaType("boolean")));
        excFlagTerm = 
            typeConv.convertToLogicElement(excFlag);
        stmnt.add(KeYJavaASTFactory.declare
                  (thrownException,
                   javaInfo.getKeYJavaType("java.lang.Throwable"))); 
        
        
        resultSubterms.add
        (normalCaseAndContinue(services, applicationPos, rule, goal, applicationSequent, contFlagTerm, returnFlagTerm,
                               breakFlagTerm, excFlagTerm, addUninterpretedPredicateIfRequired(services, inv)));
        
        Term result = createLongJunctorTerm(Junctor.AND, resultSubterms);
        
        stmnt.add(w.result());
        StatementBlock s = new StatementBlock
        (stmnt.toArray(new Statement[stmnt.size()]));
        Statement resSta;
        if (svInst.getExecutionContext() != null){
            resSta = new MethodFrame(null, svInst.getExecutionContext(), s);
        }else{
            resSta = s;
        }
        
        Modality loopBodyModality = modality;
        final boolean transaction = (loopBodyModality == Modality.DIA_TRANSACTION || loopBodyModality == Modality.BOX_TRANSACTION);
        JavaBlock mainJavaBlock = JavaBlock.createJavaBlock(transaction ? 
                                                            new StatementBlock(resSta, new TransactionStatement(de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH)) :
                                                            new StatementBlock(resSta));
        return services.getTermBuilder().prog(loopBodyModality, 
                                   mainJavaBlock, 
                                   result,
                                   computeLoopBodyModalityLabels(services, applicationPos, rule, goal, loopBodyModality, result, mainJavaBlock, applicationSequent, initialPost.getLabels())); 
    }
    
    /**
     * This method adds the uninterpreted predicate to the given {@link Term}
     * if the used {@link ProofOblInput} is an instance of {@link AbstractOperationPO}
     * and {@link AbstractOperationPO#isAddUninterpretedPredicate()} is {@code true}.
     * Otherwise the given {@link Term} is returned.  
     * @param services The {@link Services} which provides the {@link Proof} and its {@link ProofOblInput}.
     * @param term The {@link Term} to modify.
     * @return The modified or original {@link Term}.
     */
    private Term addUninterpretedPredicateIfRequired(Services services, Term term) {
       ProofOblInput problem = services.getSpecificationRepository().getProofOblInput(services.getProof());
       if (problem instanceof AbstractOperationPO) {
          AbstractOperationPO operationPO = (AbstractOperationPO)problem;
          if (operationPO.isAddUninterpretedPredicate()) {
             term = services.getTermBuilder().and(term, operationPO.getUninterpretedPredicate());
          }
       }
       return term;
    }
    
    /**
     * Computes the {@link TermLabel} which should be added to the created
     * loop body modality {@link Term}.
     * @param services The {@link Services}.
     * @param applicationPos The {@link PosInOccurrence} in the {@link Sequent} to rewrite.
     * @param rule The {@link Rule} to apply.
     * @param goal The {@link Goal} to compute the result for. 
     * @param loopBodyModality The {@link Modality} of the loop body.
     * @param result The postcondition of the modality.
     * @param mainJavaBlock The {@link JavaBlock} to execute within the modality.
     * @param applicationSequent The {@link Sequent} to rewrite.
     * @return The {@link TermLabel}s to add to the loop body modality {@link Term}.
     */
    private ImmutableArray<TermLabel> computeLoopBodyModalityLabels(Services services,
                                                                     PosInOccurrence applicationPos, 
                                                                     Rule rule, 
                                                                     Goal goal, 
                                                                     Operator loopBodyModality, 
                                                                     Term result, 
                                                                     JavaBlock mainJavaBlock, 
                                                                     Sequent applicationSequent,
                                                                     ImmutableArray<TermLabel> newTermOriginalLabels) {
       return TermLabelManager.instantiateLabels(services, applicationPos, rule, goal, "LoopBodyModality", null, loopBodyModality, new ImmutableArray<Term>(result), null, mainJavaBlock, newTermOriginalLabels);
    }

    /**
     * creates a new program variable 
     * @param varNameBase a String specifying the basename of the new variable
     * @param varType a String specifying the typename of the new variable 
     * @param services the Services allowing access to the variablenaming facilities
     * @return a new program variable of the given type and a name as near as possible
     * to the given basename
     */
    private ProgramVariable getNewLocalvariable
    (String varNameBase, String varType, Services services) {
        
        return getNewLocalvariable(varNameBase, 
                                   javaInfo.getKeYJavaType(varType), services);
        
    }
    
    /**
     * creates a new program variable 
     * @param varNameBase a String specifying the basename of the new variable
     * @param varType the KeYJavaType of the new variable 
     * @param services the Services allowing access to the variablenaming facilities
     * @return a new program variable of the given type and a name as near as possible
     * to the given basename
     */
    private ProgramVariable getNewLocalvariable
    (String varNameBase, KeYJavaType varType, Services services) {        
        return KeYJavaASTFactory.
          localVariable(services.getVariableNamer().
                        getTemporaryNameProposal(varNameBase), varType);
        
    }
    

    /** returns the schemavariables that are needed to transform the given
     * loop. The unwind-loop construct may need labels if unlabeled breaks 
     * and/or continues occur in the loop. Often there will be uninstantiated
     * Schemavariables in the loop that is why the found instantiations have to
     * be given.
     */
    public ImmutableList<SchemaVariable> neededInstantiations(ProgramElement originalLoop,
                                                     SVInstantiations svInst) {
        WhileInvariantTransformation w = 
	    new WhileInvariantTransformation(originalLoop, 
                                             svInst, 
                                             javaInfo == null 
                                              ? null 
                                              : javaInfo.getServices());
        w.start();
        instantiations = ImmutableSLList.<SchemaVariable>nil();
        if (w.innerLabelNeeded()) {
            instantiations = instantiations.prepend(innerLabel);
        }
        if (w.outerLabelNeeded()) {
            instantiations = instantiations.prepend(outerLabel);
        }
        breakList = w.breakList();
        return instantiations;
    }

    //---------------------------------------------------------------
    // --- private helper methods to construct the result term
    //---------------------------------------------------------------


    private Term createLongJunctorTerm(Junctor junctor, ArrayList<Term> terms) {
        if (terms.size() == 1)
            return terms.get(0);
        else if (terms.size() == 2)
            return tf.createTerm(junctor, terms.get(0), terms.get(1));
        else {
            Term arg1 = terms.get(0);
            terms.remove(0);
            return 
                tf.createTerm(junctor, 
                                     arg1, 
                                     createLongJunctorTerm(junctor, terms));
        }
    }


    private Statement returnFlagDecl(ProgramVariable returnFlag,
                                     SVInstantiations svInst) {
        return KeYJavaASTFactory.
            declare(returnFlag, BooleanLiteral.FALSE,
                    javaInfo.getKeYJavaType("boolean"));
    }

    private Term returnCase(ProgramVariable returnFlag,
                            KeYJavaType returnType,
                            ProgramVariable returnExpression,
                            Term post,
                            WhileInvariantRule rule, 
                            Goal goal,
                            PosInOccurrence applicationPos, 
                            Services services) {
        JavaBlock returnJavaBlock = addContext(root, new StatementBlock(KeYJavaASTFactory.returnClause(returnExpression)));
        Term executeReturn = services.getTermBuilder().prog(modality, 
                                                 returnJavaBlock, 
                                                 post,
                                                 TermLabelManager.instantiateLabels(services, applicationPos, rule, goal, "ReturnCaseModality", null, modality, new ImmutableArray<Term>(post), null, returnJavaBlock, post.getLabels()));
        
        return services.getTermBuilder().imp(services.getTermBuilder().equals(typeConv.convertToLogicElement(returnFlag), typeConv.getBooleanLDT().getTrueTerm()),
                                  executeReturn);
    }


    private Statement breakFlagDecl(ProgramVariable breakFlag) {
        return KeYJavaASTFactory.
            declare(breakFlag, BooleanLiteral.FALSE,
                    javaInfo.getKeYJavaType("boolean"));
    }

    private Statement contFlagDecl(ProgramVariable contFlag) {
        return KeYJavaASTFactory.
            declare(contFlag, BooleanLiteral.FALSE,
                    javaInfo.getKeYJavaType("boolean"));
    }

    private Term breakCase(ProgramVariable breakFlag,
                           Term post,
                           ArrayList<If> breakIfCascade,
                           WhileInvariantRule rule, 
                           Goal goal,
                           PosInOccurrence applicationPos, 
                           Services services) {
        JavaBlock executeJavaBlock = addContext(root, new StatementBlock(breakIfCascade.toArray(new Statement[breakIfCascade.size()])));
        Term executeBreak = services.getTermBuilder().prog(modality, 
                                                executeJavaBlock, 
                                                post,
                                                TermLabelManager.instantiateLabels(services, applicationPos, rule, goal, "BreakCaseModality", null, modality, new ImmutableArray<Term>(post), null, executeJavaBlock, post.getLabels()));
        return services.getTermBuilder().imp(services.getTermBuilder().equals(typeConv.convertToLogicElement(breakFlag), 
                                typeConv.getBooleanLDT().getTrueTerm()), 
                                executeBreak); 
    }


    private Term  normalCaseAndContinue(Services services,
                                        PosInOccurrence applicationPos,
                                        Rule rule,
                                        Goal goal,
                                        Sequent applicationSequent,
                                        Term contFlagTerm,
                                        Term returnFlagTerm,
                                        Term breakFlagTerm,
                                        Term excFlagTerm,
                                        Term inv) {

        final TermBuilder TB = services.getTermBuilder();
        final Term TRUE_TERM = typeConv.getBooleanLDT().getTrueTerm();

        ArrayList<Term> al = new ArrayList<Term>();

        if (returnFlagTerm != null)
            al.add(TB.equals(returnFlagTerm, TRUE_TERM));
        if (breakFlagTerm != null)
            al.add(TB.equals(breakFlagTerm, TRUE_TERM));
        if (excFlagTerm != null)
            al.add(TB.equals(excFlagTerm, TRUE_TERM));

        if (al.size() == 0) {
            if (contFlagTerm == null) {
                ImmutableArray<TermLabel> labels = computeLoopBodyImplicatonLabels(services, applicationPos, rule, goal, inv.op(), inv.subs(), applicationSequent);
                return TB.label(inv, labels);
            }
            else {
                ImmutableArray<TermLabel> labels = computeLoopBodyImplicatonLabels(services, applicationPos, rule, goal, Junctor.IMP, new ImmutableArray<Term>(contFlagTerm, inv), applicationSequent);
                return TB.imp(contFlagTerm, inv, labels);
            }
        } else {
            Term premiss = TB.not(createLongJunctorTerm(Junctor.OR, al));
            if (contFlagTerm != null)
                premiss = TB.imp(contFlagTerm, premiss);            
            
            ImmutableArray<TermLabel> labels = computeLoopBodyImplicatonLabels(services, applicationPos, rule, goal, Junctor.IMP, new ImmutableArray<Term>(premiss, inv), applicationSequent);
            return TB.imp(premiss, inv, labels);
        }       
    }
    
    /**
     * Computes the {@link TermLabel} which should be added to the implication
     * of the normal termination branch of a loop body.
     * @param services The {@link Services}.
     * @param applicationPos The {@link PosInOccurrence} in the {@link Sequent} to rewrite.
     * @param rule The {@link Rule} to apply.
     * @param goal The {@link Goal} to compute the result for. 
     * @param operator The {@link Operator} of the new {@link Term}.
     * @param subs The children of the new {@link Term}.
     * @param applicationSequent The {@link Sequent} to rewrite.
     * @return The {@link TermLabel}s to add to the new {@link Term}.
     */
    private ImmutableArray<TermLabel> computeLoopBodyImplicatonLabels(Services services,
                                                                       PosInOccurrence applicationPos, 
                                                                       Rule rule, 
                                                                       Goal goal, 
                                                                       Operator operator, 
                                                                       ImmutableArray<Term> subs, 
                                                                       Sequent applicationSequent) {
       return TermLabelManager.instantiateLabels(services, applicationPos, rule, goal, "LoopBodyImplication", null, operator, subs, null, null, post.getLabels());
    }
    

    private Term throwCase(ProgramVariable excFlag,
                           ProgramVariable thrownException,
                           Term post,
                           WhileInvariantRule rule, 
                           Goal goal,
                           PosInOccurrence applicationPos, 
                           Services services) {
        final TermBuilder TB = services.getTermBuilder();
        JavaBlock throwJavaBlock = addContext(root, new StatementBlock(KeYJavaASTFactory.throwClause(thrownException)));
        Term throwException = TB.prog(modality, 
                                                  throwJavaBlock, 
                                                  post,
                                                  TermLabelManager.instantiateLabels(services, applicationPos, rule, goal, "ThrowCaseModality", null, modality, new ImmutableArray<Term>(post), null, throwJavaBlock, post.getLabels()));
        return TB.imp( 
              TB.equals(typeConv.convertToLogicElement(excFlag), 
        	       typeConv.getBooleanLDT().getTrueTerm()), 
             throwException);
    }


    protected JavaBlock addContext(JavaNonTerminalProgramElement root,
                                   StatementBlock block) {
        ReplaceWhileLoop replaceWhile = 
  	    new ReplaceWhileLoop(root, block, javaInfo.getServices());
        replaceWhile.start();       
        
        return JavaBlock.createJavaBlock((StatementBlock)replaceWhile.result());

    }
}