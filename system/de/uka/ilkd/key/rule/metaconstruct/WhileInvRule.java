// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;


import java.util.ArrayList;
import java.util.LinkedList;
import java.util.ListIterator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class WhileInvRule extends AbstractMetaOperator {

    /** the outer label that is used to leave the while loop ('l1') */
    private final SchemaVariable outerLabel = 
        SchemaVariableFactory.createProgramSV(new ProgramElementName("outer_label"),
                                       ProgramSVSort.LABEL, false);
    /** the inner label ('l2') */
    private final SchemaVariable innerLabel =
        SchemaVariableFactory.createProgramSV(new ProgramElementName("inner_label"),
                                       ProgramSVSort.LABEL, false);
    /** list of the labels */
    private ListOfSchemaVariable instantiations  = null;

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
    
    public WhileInvRule() {
        super(new Name("#whileInvRule"), 2);
    }


    /** Unlike other meta operators this one returns a formula
     * not a term.
     */
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }


    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
        // a meta operator accepts almost everything
        return  term.arity()==arity();
    }


   
    /**
     * initialises this meta operator
     * @param term the instantiated Term passed to the MetaOperator 
     * @param services the Services providing access to signature and
     * type model
     */
    private void init(Term term, Services services) {
        root = (JavaNonTerminalProgramElement)
        term.sub(0).javaBlock().program();  
        modality = (Modality)term.sub(0).op();
        
        ReplaceWhileLoop removeWhile = 
            new ReplaceWhileLoop(root, null, services);
        removeWhile.start();       
        
        body = removeWhile.getTheLoop();
        
        // some initialisations...
                
        inv = term.sub(1);
        post = term.sub(0).sub(0);
                        
        javaInfo = services.getJavaInfo();
        tf = TermFactory.DEFAULT ;
        typeConv = services.getTypeConverter();
        
        returnType = removeWhile.returnType();
    }
    
    
    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        
        // global initialisation
        init(term, services);
        
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
            new WhileInvariantTransformation((While)body, 
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
            contFlagTerm = tf.createEqualityTerm
            (Op.EQUALS, 
             typeConv.convertToLogicElement(contFlag), 
             typeConv.getBooleanLDT().getTrueTerm());
        }
        
        // exception case
        resultSubterms.add(throwCase(excFlag, 
                                     thrownException, 
                                     post));
        
        // return case
        if (w.returnOccurred()) {
            stmnt.add(returnFlagDecl(returnFlag, svInst));
            returnFlagTerm = 
                typeConv.convertToLogicElement(returnFlag);
            resultSubterms.add
            (returnCase(returnFlag, returnType,
                        returnExpression, post));
            
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
                                         breakIfCascade)); 
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
        (normalCaseAndContinue(contFlagTerm, returnFlagTerm,
                               breakFlagTerm, excFlagTerm, inv));
        
        Term result = createLongJunctorTerm(Op.AND, resultSubterms); 
        
        stmnt.add(w.result());
        StatementBlock s = new StatementBlock
        (stmnt.toArray(new Statement[0]));
        Statement resSta;
        if (svInst.getExecutionContext() != null){
            resSta = new MethodFrame(null, svInst.getExecutionContext(), s);
        }else{
            resSta = s;
        }
        
        Modality loopBodyModality = modality;
        
        return tf.createProgramTerm
        (loopBodyModality, 
         JavaBlock.createJavaBlock
         (new StatementBlock(resSta)), result); 
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
    public ListOfSchemaVariable neededInstantiations(ProgramElement originalLoop,
                                                     SVInstantiations svInst) {
        WhileInvariantTransformation w = 
	    new WhileInvariantTransformation(originalLoop, 
                                             svInst, 
                                             javaInfo == null 
                                              ? null 
                                              : javaInfo.getServices());
        w.start();
        instantiations = SLListOfSchemaVariable.EMPTY_LIST;
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
            return tf.createJunctorTerm(junctor,
                                        terms.get(0),
                                        terms.get(1));
        else {
            Term arg1 = terms.get(0);
            terms.remove(0);
            return 
                tf.createJunctorTerm(junctor, 
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
                            Term post) {
        Term executeReturn = tf.createProgramTerm
            (modality, 
             addContext(root, new StatementBlock
                        (KeYJavaASTFactory.returnClause(returnExpression))), 
             post);
        
        return tf.createJunctorTerm
            (Op.IMP, 
             tf.createEqualityTerm(Op.EQUALS, 
                                   typeConv.convertToLogicElement(returnFlag), 
                                   typeConv.getBooleanLDT().getTrueTerm()), 
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
                           ArrayList<If> breakIfCascade) {
        Term executeBreak = 
            tf.createProgramTerm
            (modality,
             addContext(root, new StatementBlock
                        (breakIfCascade.toArray(new Statement[0]))),
             post);
        return tf.createJunctorTerm
            (Op.IMP, 
             tf.createEqualityTerm(Op.EQUALS, 
                                   typeConv.convertToLogicElement(breakFlag), 
                                   typeConv.getBooleanLDT().getTrueTerm()), 
             executeBreak); 
    }


    private Term  normalCaseAndContinue(Term contFlagTerm,
                                        Term returnFlagTerm,
                                        Term breakFlagTerm,
                                        Term excFlagTerm,
                                        Term inv) {

        final Term TRUE_TERM = typeConv.getBooleanLDT().getTrueTerm();

        ArrayList<Term> al = new ArrayList<Term>();

        if (returnFlagTerm != null)
            al.add(tf.createEqualityTerm(Op.EQUALS, returnFlagTerm, TRUE_TERM));
        if (breakFlagTerm != null)
            al.add(tf.createEqualityTerm(Op.EQUALS, breakFlagTerm, TRUE_TERM));
        if (excFlagTerm != null)
            al.add(tf.createEqualityTerm(Op.EQUALS, excFlagTerm, TRUE_TERM));

        if (al.size() == 0) {
            if (contFlagTerm == null)
                return inv;
            else 
                return tf.createJunctorTerm(Op.IMP, contFlagTerm, inv);
        } else {
            Term premiss = tf.createJunctorTerm(Op.NOT, 
                                                createLongJunctorTerm(Op.OR, al));
            if (contFlagTerm != null)
                premiss = tf.createJunctorTerm(Op.OR, 
                                               contFlagTerm,
                                               premiss);            
            
            return 
                tf.createJunctorTerm(Op.IMP, premiss, inv);
        }       
    }
    

    private Term throwCase(ProgramVariable excFlag,
                           ProgramVariable thrownException,
                           Term post) {
        Term throwException = 
            tf.createProgramTerm
            (modality, addContext
             (root, new StatementBlock
              (KeYJavaASTFactory.throwClause(thrownException))), 
             post);
        return tf.createJunctorTerm
            (Op.IMP, 
             tf.createEqualityTerm(Op.EQUALS, 
                                   typeConv.convertToLogicElement(excFlag), 
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
