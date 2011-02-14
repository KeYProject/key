// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
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
import java.util.List;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * 
 * This class implements the meta operator that is used to implement the
 * invariant rule for the enhanced for loop of Java 5.
 * 
 * It is strongly related to {@link WhileInvRule}.
 * 
 * The operator takes four arguments:
 * <ol>
 * <li>a modality formula. The program is a foreach loop + context
 * <li>the invariant term after the loop body has been executed, i.e. with 
 * the variable incremented.
 * <li>the variable term that is used as index
 * <li>the array expression to be used.
 * </ol>
 * 
 * @author mulbrich
 */

public final class EnhancedForInvRule extends AbstractMetaOperator {

    private static final boolean FORMALPARAM_AS_STATEMENT = false;
    private static final TermBuilder TB = TermBuilder.DF;    

    /*
     * list of breaks that lead to abrupt termination of the loop to be
     * transformed. Is initialised by the method neededInstantiations that is
     * invoked before calculate
     */
    private LinkedList<BreakToBeReplaced> breakList;

    /**
     * The JavaInfo object which is handed over as a parameter of calculate.
     */
    private JavaInfo javaInfo;

    /**
     * the type converter - taken from services
     */
    private TypeConverter typeConv;

    /**
     * term factory to be used - from the services
     */
    private TermFactory tf;
    
    /**
     * the services provided at init()
     */
    private Services services;

    /**
     * the for loop under inspection
     */
    private EnhancedFor loop;

    /**
     * the invariant
     */
    private Term inv;

    /**
     * the post condition
     */
    private Term post;

    /**
     * the counter variable, that is implicitly used in an enhanced for loop
     */
    private Term counter;

    /**
     * the array variable that is implicitly used in an enhanced for loop
     */
    private Term arrayvar;

    /**
     * the entire program as a pointer to its base
     */
    private JavaNonTerminalProgramElement root;

    /**
     * the used modality
     */
    private Modality modality;

    /**
     * if the while loop is in a methodframe, this is the return type of the
     * method referenced by the method frame.
     */
    private KeYJavaType returnType;

    /**
     * the traversed array expresion. It is stored in the guard field of the
     * enhanced for loop. It is extracted from the loop - argument #1.
     */
    private Expression arrayexp;

    /**
     * the formal parameter from the variable declaration within the enh. for
     * loop - extracted from the loop.
     */
    private VariableSpecification formalParam;

    

    /**
     * create an instance of this rule.
     * 
     * It has arity 4: 1) the program to be treated 2) the invariant 3) the name
     * of the implicit counter variable 4) the array term to be used
     * 
     */
    public EnhancedForInvRule() {
        super(new Name("#foreachInvRule"), 4, Sort.FORMULA);
    }


    /**
     * initialises this meta operator.
     * 
     * Extract from the given term: - loop - inv - post
     * 
     * @param term
     *            the instantiated Term passed to the MetaOperator
     * @param services
     *            the Services providing access to signature and type model
     */
    private void init(Term term, Services services) {
        
        this.services = services;
        
        root =
                (JavaNonTerminalProgramElement) term.sub(0).javaBlock().program();
        modality = (Modality) term.sub(0).op();

        ReplaceWhileLoop removeWhile = new ReplaceWhileLoop(root, null, services);
        removeWhile.start();
        loop = (EnhancedFor) removeWhile.getTheLoop();

        inv = term.sub(1);
        post = term.sub(0).sub(0);
        counter = /* (ProgramVariable) */term.sub(2); // .op();
        arrayvar = term.sub(3);

        javaInfo = services.getJavaInfo();
        tf = TermFactory.DEFAULT;
        typeConv = services.getTypeConverter();

        // the loop is an enhanced for loop
        arrayexp = loop.getGuardExpression();
        LocalVariableDeclaration lvd =
                (LocalVariableDeclaration) loop.getILoopInit().getInits().get(0);
        formalParam =
                lvd.getVariableSpecifications().get(0);

        returnType = removeWhile.returnType();
    }

    /**
     * calculates the resulting term.
     * 
     * 
     * 
     * @see de.uka.ilkd.key.logic.op.AbstractMetaOperator#calculate(de.uka.ilkd.key.logic.Term,
     *      de.uka.ilkd.key.rule.inst.SVInstantiations,
     *      de.uka.ilkd.key.java.Services)
     */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {

        // global initialisation
        init(term, services);

        /*
         * list of local initialisations. all newly created vars must be
         * initialised
         */
        List<Statement> stmnt = new ArrayList<Statement>();

        /*
         * List of statements of the form: "if(brk#n) break label;"
         */
        ArrayList<If> breakIfCascade = new ArrayList<If>();

        // termination flags
        ProgramVariable contFlag =
                getNewLocalvariable("cont", "boolean", services);
        ProgramVariable returnFlag =
                getNewLocalvariable("rtrn", "boolean", services);
        ProgramVariable breakFlag =
                getNewLocalvariable("brk", "boolean", services);
        ProgramVariable excFlag =
                getNewLocalvariable("exc", "boolean", services);
        ProgramVariable excParam =
                getNewLocalvariable("e", "java.lang.Throwable", services);
        ProgramVariable thrownException =
                getNewLocalvariable("thrownExc", "java.lang.Throwable",
                        services);
        ProgramVariable returnExpression = null;
        if (returnType != null) {
            returnExpression =
                    getNewLocalvariable("returnExpr", returnType, services);
        }

        Term contFlagTerm = null;
        Term returnFlagTerm = null;
        Term breakFlagTerm = null;
        Term excFlagTerm = null;

        // end of initialisation

        // 2 runs of the transformation: detect breaks and transform them
        // could be done in 1 pass - but inherits from while
        ProgramElementName labelName = null;

        WhileInvariantTransformation w =
                new WhileInvariantTransformation(loop, svInst, services);
        w.start();

        if (w.innerLabelNeeded() || w.outerLabelNeeded()) {
            labelName =
                    services.getVariableNamer().getTemporaryNameProposal(
                            "label");
        }
        breakList = w.breakList();

        //
        // create a variable for each label, to reproduce the break
        int numberOfBreaks = breakList.size();
        int breakCounter = 0;
        for (BreakToBeReplaced b : breakList) {
            ProgramVariable newVar =
                    getNewLocalvariable("brk_" + breakCounter++, "boolean",
                            services);
            b.setProgramVariable(newVar);
            stmnt.add(KeYJavaASTFactory.declare(newVar, BooleanLiteral.FALSE,
                    javaInfo.getKeYJavaType("boolean")));
            Statement s;
            if (b.getBreak().getLabel() != null)
                s = KeYJavaASTFactory.breakStatement(b.getBreak().getLabel());
            else
                s = KeYJavaASTFactory.emptyStatement();
            breakIfCascade.add(KeYJavaASTFactory.ifThen(newVar, s));
        }

        //
        // 2nd run
        w =
                new WhileInvariantTransformation(loop, labelName, labelName,
                        contFlag, excFlag, excParam, thrownException,
                        breakFlag, returnFlag, returnExpression, breakList,
                        services);
        w.start();

        /*
         * A list of resulting subterms that are "anded" in the end
         */
        ArrayList<Term> resultSubterms = new ArrayList<Term>();

        //
        // exception case
        resultSubterms.add(throwCase(excFlag, thrownException, post));
        excFlagTerm = typeConv.convertToLogicElement(excFlag);
        stmnt.add(KeYJavaASTFactory.declare(excFlag, BooleanLiteral.FALSE,
                javaInfo.getKeYJavaType("boolean")));
        stmnt.add(KeYJavaASTFactory.declare(thrownException,
                javaInfo.getKeYJavaType("java.lang.Throwable")));

        //
        // return case
        if (w.returnOccurred()) {
            stmnt.add(returnFlagDecl(returnFlag));
            returnFlagTerm = typeConv.convertToLogicElement(returnFlag);
            resultSubterms.add(returnCase(returnFlag, returnType,
                    returnExpression, post));

            if (returnType != null) {
                stmnt.add(KeYJavaASTFactory.declare(returnExpression,
                        returnType));
            }
        }

        //
        // break case
        if (numberOfBreaks > 0) {
            stmnt.add(breakFlagDecl(breakFlag));
            breakFlagTerm = typeConv.convertToLogicElement(breakFlag);
            resultSubterms.add(breakCase(breakFlag, post, breakIfCascade));
        }

        //
        // normal case and continue
        if (w.continueOccurred()) {
            stmnt.add(contFlagDecl(contFlag));
            contFlagTerm = TB.equals(typeConv.convertToLogicElement(contFlag),
                                     TB.tt());
        }
        resultSubterms.add(normalCaseAndContinue(contFlagTerm, returnFlagTerm,
                breakFlagTerm, excFlagTerm, inv));

        Term result = createLongJunctorTerm(Junctor.AND, resultSubterms);

        if (FORMALPARAM_AS_STATEMENT) {
            //
            // add the formal parameter declaration to the statement block
            ProgramVariable varname =
                    (ProgramVariable) formalParam.getProgramVariable();
            Type type = formalParam.getType();
            ArrayReference ar =
                    new ArrayReference((ReferencePrefix) arrayexp,
                            new Expression[] { (ProgramVariable) counter.op() });

            LocalVariableDeclaration decl =
                    KeYJavaASTFactory.declare(varname, ar,
                            varname.getKeYJavaType());
            stmnt.add(decl);

        }
        //
        // make statement block, possibly within a method frame
        stmnt.add((Statement) w.result());
        StatementBlock s =
                new StatementBlock(
                        stmnt.toArray(new Statement[stmnt.size()]));
        Statement resSta;
        if (svInst.getExecutionContext() != null)
            resSta = new MethodFrame(null, svInst.getExecutionContext(), s);
        else
            resSta = s;

        Modality loopBodyModality = modality;

        final Term resultTerm =
                TB.prog(loopBodyModality,
                       JavaBlock.createJavaBlock(new StatementBlock(resSta)),
                       result);

        if (FORMALPARAM_AS_STATEMENT) {
            return resultTerm;
        } else {
            // OR add the formal parameter declaration as an update

            Term arrayAccess = TB.dotArr(services, arrayvar, counter);
            ProgramVariable var =
                    (ProgramVariable) formalParam.getProgramVariable();
            return TB.applyElementary(services, TB.var(var), arrayAccess, resultTerm);
        }

    }

    /**
     * creates a new program variable
     * 
     * @param varNameBase
     *            a String specifying the basename of the new variable
     * @param varType
     *            a String specifying the typename of the new variable
     * @param services
     *            the Services allowing access to the variablenaming facilities
     * @return a new program variable of the given type and a name as near as
     *         possible to the given basename
     */
    private ProgramVariable getNewLocalvariable(String varNameBase,
            String varType, Services services) {

        return getNewLocalvariable(varNameBase,
                javaInfo.getKeYJavaType(varType), services);

    }

    /**
     * creates a new program variable
     * 
     * @param varNameBase
     *            a String specifying the basename of the new variable
     * @param varType
     *            the KeYJavaType of the new variable
     * @param services
     *            the Services allowing access to the variablenaming facilities
     * @return a new program variable of the given type and a name as near as
     *         possible to the given basename
     */
    private ProgramVariable getNewLocalvariable(String varNameBase,
            KeYJavaType varType, Services services) {
        return KeYJavaASTFactory.localVariable(
                services.getVariableNamer().getTemporaryNameProposal(
                        varNameBase), varType);

    }

    // ---------------------------------------------------------------
    // --- private helper methods to construct the result term
    // ---------------------------------------------------------------

    private Term createLongJunctorTerm(Junctor junctor, ArrayList<Term> terms) {
        if (terms.size() == 1)
            return terms.get(0);
        else if (terms.size() == 2)
            return tf.createTerm(junctor, terms.get(0),
                    terms.get(1));
        else {
            Term arg1 = terms.get(0);
            terms.remove(0);
            return tf.createTerm(junctor, arg1, createLongJunctorTerm(
                    junctor, terms));
        }
    }

    /*
     * make declarations like:
     * 
     * <pre> boolean flag = false; </pre>
     */
    private Statement returnFlagDecl(ProgramVariable returnFlag) {
        return KeYJavaASTFactory.declare(returnFlag, BooleanLiteral.FALSE,
                javaInfo.getKeYJavaType("boolean"));
    }

    private Statement breakFlagDecl(ProgramVariable breakFlag) {
        return KeYJavaASTFactory.declare(breakFlag, BooleanLiteral.FALSE,
                javaInfo.getKeYJavaType("boolean"));
    }

    private Statement contFlagDecl(ProgramVariable contFlag) {
        return KeYJavaASTFactory.declare(contFlag, BooleanLiteral.FALSE,
                javaInfo.getKeYJavaType("boolean"));
    }

    /**
     * build that term that handles the case that a break statement has been
     * encountered.
     * 
     * Not every break is necessarily important here.
     * {@link WhileInvariantTransformation} will handle this.
     * 
     * Like:
     * 
     * <pre>
     *               breakFlag = TRUE -&gt; \<{ .. if(br1) break label1; 
     *                                             if(br2) break label2
     *                                             /and so on/    ... }\>post
     * </pre>
     * 
     * @param breakFlag
     *            flag indicating a "break"
     * @param post
     *            the post condition that needs to hold
     * @param breakIfCascade
     *            the cascade that makes a case distinction between different
     *            breaks.
     * @return the term that puts this together
     */
    private Term breakCase(ProgramVariable breakFlag, Term post,
            ArrayList<If> breakIfCascade) {
        Term executeBreak =
                TB.prog(
                        modality,
                        addContext(
                                root,
                                new StatementBlock(
                                        breakIfCascade.toArray(new Statement[breakIfCascade.size()]))),
                        post
                        );
        return TB.imp(TB.equals(
                typeConv.convertToLogicElement(breakFlag),
                typeConv.getBooleanLDT().getTrueTerm()), executeBreak);
    }

    /**
     * If the block terminates normally or with continue, the invariant must
     * hold.
     * 
     * This is specific to EnhancedFors: {i := i+1}
     * 
     * <pre>
     *             !(ret = TRUE | brk = TRUE | exc = TRUE) -&gt; 
     *                       {i := i + 1}Inv
     * </pre>
     * 
     * with i the counter variabele.
     * 
     * Continue flag is not needed, historically there.
     * 
     * @param returnFlagTerm
     *            the term used to indicate return or null if no return has
     *            appeared
     * @param breakFlagTerm
     *            the term used to indicate break or null if no break has
     *            appeared
     * @param excFlagTerm
     *            the flag used to indicate exceptions
     * @param inv
     *            the invariant that has to hold afterwards
     */
    private Term normalCaseAndContinue(Term contFlagTerm, Term returnFlagTerm,
            Term breakFlagTerm, Term excFlagTerm, Term inv) {

        final Term TRUE_TERM = typeConv.getBooleanLDT().getTrueTerm();

        ArrayList<Term> al = new ArrayList<Term>();

        if (returnFlagTerm != null)
            al.add(TB.equals(returnFlagTerm, TRUE_TERM));
        if (breakFlagTerm != null)
            al.add(TB.equals(breakFlagTerm, TRUE_TERM));
        if (excFlagTerm != null)
            al.add(TB.equals(excFlagTerm, TRUE_TERM));

        if (al.size() == 0) {
            return inv;
        } else {
            return TB.imp(TB.not(createLongJunctorTerm(Junctor.OR, al)), inv);
        }
    }

    /**
     * 
     * build that term that handles the case that a value is returned from a
     * method frame to the level above.
     * 
     * Like:
     * 
     * <pre>
     *               returnFlag = TRUE -&gt; \&lt;{ .. return returnExpression ... }\&gt;post
     * </pre>
     * 
     * @param returnFlag
     *            flag indicating a "return"
     * @param returnType
     *            the type to be returned
     * @param returnExpression
     *            the expression to be return
     * @param post
     *            the post condition that needs to hold
     * @return the term that puts this together
     */
    private Term returnCase(ProgramVariable returnFlag, KeYJavaType returnType,
            ProgramVariable returnExpression, Term post) {
        Term executeReturn =
                TB.prog(
                        modality,
                        addContext(
                                root,
                                new StatementBlock(
                                        KeYJavaASTFactory.returnClause(returnExpression))),
                        post);

        return TB.imp(TB.equals(
                typeConv.convertToLogicElement(returnFlag),
                typeConv.getBooleanLDT().getTrueTerm()), executeReturn);

    }

    /**
     * build that term that handles the case that an exception has been thrown.
     * 
     * Like:
     * 
     * <pre>
     *            exc = TRUE -&gt; \&lt;{ .. throw  thrownException ... }\&gt;post
     * </pre>
     * 
     * @param excFlag
     *            flag indicating exception
     * @param thrownException
     *            the exception that has been thrown in that case
     * @param post
     *            the post condition that needs to hold
     * @return the term that puts this together
     */
    private Term throwCase(ProgramVariable excFlag,
            ProgramVariable thrownException, Term post) {
        Term throwException =
                TB.prog( modality,
                        addContext(root, new StatementBlock(
                                KeYJavaASTFactory.throwClause(thrownException))),
                        post);
        return TB.imp(TB.equals(
                typeConv.convertToLogicElement(excFlag),
                typeConv.getBooleanLDT().getTrueTerm()), throwException);
    }

    /**
     * Replace the top most loop in a block with some statement block.
     * 
     * So the block has the same context as the for loop originally had.
     * 
     * @param root
     *            the ProgramElement that contains the loop
     * @param block
     *            the block to replace with
     * @return the new java block
     */
    protected JavaBlock addContext(JavaNonTerminalProgramElement root,
            StatementBlock block) {
        ReplaceWhileLoop replaceWhile = new ReplaceWhileLoop(root, block, services);
        replaceWhile.start();

        return JavaBlock.createJavaBlock((StatementBlock) replaceWhile.result());

    }
}
