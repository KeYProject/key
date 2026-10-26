/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.Iterator;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.Modifier;
import de.uka.ilkd.key.java.ast.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.Assignment;
import de.uka.ilkd.key.java.ast.expression.BinaryAssignment;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.ast.expression.operator.New;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.statement.Branch;
import de.uka.ilkd.key.java.ast.statement.Catch;
import de.uka.ilkd.key.java.ast.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.ast.statement.Try;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 *
 * @author christoph
 */
@NullMarked
class BasicSymbolicExecutionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        assert poVars.exceptionParameter.op() instanceof LocationVariable
                : "Something is wrong with the catch variable";

        ImmutableList<JTerm> posts = ImmutableList.nil();
        if (poVars.post.self != null && poVars.pre.self != null) {
            posts = posts.append(d.tb.equals(poVars.post.self, poVars.pre.self));
        }
        if (poVars.post.result != null && poVars.pre.result != null) {
            posts = posts.append(d.tb.equals(poVars.post.result, poVars.pre.result));
        }
        if (poVars.post.exception != null && poVars.pre.exception != null) {
            posts = posts.append(d.tb.equals(poVars.post.exception, poVars.pre.exception));
        }
        posts = posts.append(d.tb.equals(poVars.post.heap, d.tb.getBaseHeap()));
        return buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
    }

    private JTerm buildProgramTerm(BasicSnippetData d, ProofObligationVars vs, JTerm postTerm,
            TermBuilder tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "program-term for a contract without modality.");
        }
        assert JModality.JavaModalityKind.class.equals(BasicSnippetData.Key.MODALITY.getType());
        JModality.JavaModalityKind kind =
            (JModality.JavaModalityKind) d.get(BasicSnippetData.Key.MODALITY);


        // create java block
        final ImmutableList<JTerm> formalParams = vs.formalParams;
        if (formalParams == null) {
            throw new NullPointerException(
                "No formal parameter terms for the symbolic execution block.");
        }
        final JavaBlock jb = buildJavaBlock(d, formalParams,
            vs.pre.self != null ? vs.pre.self.op(ProgramVariable.class) : null,
            vs.pre.result != null ? vs.pre.result.op(ProgramVariable.class) : null,
            vs.pre.exception != null ? vs.pre.exception.op(ProgramVariable.class) : null,
            vs.exceptionParameter.op(LocationVariable.class));

        // create program term
        final JModality.JavaModalityKind symbExecMod;
        if (kind == JModality.JavaModalityKind.BOX) {
            symbExecMod = JModality.JavaModalityKind.DIA;
        } else {
            symbExecMod = JModality.JavaModalityKind.BOX;
        }
        final JTerm programTerm = tb.prog(symbExecMod, jb, postTerm);
        // final Term programTerm = tb.not(tb.prog(modality, jb, tb.not(postTerm)));

        // create update
        JTerm update = tb.skip();
        Iterator<JTerm> formalParamIt = formalParams.iterator();
        Iterator<JTerm> paramIt = vs.pre.localVars.iterator();
        while (formalParamIt.hasNext()) {
            JTerm formalParam = formalParamIt.next();
            LocationVariable formalParamVar = formalParam.op(LocationVariable.class);
            JTerm paramUpdate = tb.elementary(formalParamVar, paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }

        return tb.apply(update, programTerm);
    }

    private JavaBlock buildJavaBlock(BasicSnippetData d, ImmutableList<JTerm> formalPars,
            @Nullable ProgramVariable selfVar, @Nullable ProgramVariable resultVar,
            @Nullable ProgramVariable exceptionVar, LocationVariable eVar) {
        IObserverFunction targetMethod =
            (IObserverFunction) d.get(BasicSnippetData.Key.TARGET_METHOD);
        if (!(targetMethod instanceof IProgramMethod pm)) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "java-block for an observer which is no program method.");
        }
        JavaInfo javaInfo = d.services.getJavaInfo();

        // create method call
        ProgramVariable[] formalParVars = extractProgramVariables(formalPars);
        final ImmutableArray<Expression> formalArray =
            new ImmutableArray<>(formalParVars);
        final StatementBlock sb;
        if (pm.isConstructor()) {
            if (selfVar == null) {
                throw new NullPointerException(
                    "No self variable for a constructor's symbolic execution block.");
            }
            assert resultVar == null : "Constructor snippets must not bind a result variable.";
            final Expression[] formalArray2 =
                formalArray.toArray(new Expression[formalArray.size()]);
            KeYJavaType forClass = (KeYJavaType) d.get(BasicSnippetData.Key.FOR_CLASS);
            if (forClass == null) {
                throw new NullPointerException(
                    "No target type for a constructor's symbolic execution block.");
            }
            final New n = new New(formalArray2, new TypeRef(forClass), null);
            final Assignment ca = new BinaryAssignment(selfVar, n);
            sb = new StatementBlock(ca);
        } else {
            final MethodBodyStatement call =
                buildMethodBodyStatement(pm, selfVar, resultVar, formalArray);
            sb = new StatementBlock(call);
        }

        // type of the variable for the try statement
        final KeYJavaType eType = javaInfo.getTypeByClassName("java.lang.Throwable");
        if (eType == null) {
            throw new NullPointerException("No type for java.lang.Throwable.");
        }
        final TypeReference excTypeRef = javaInfo.createTypeReference(eType);

        // create try statement
        if (exceptionVar == null) {
            throw new NullPointerException("No exception variable for the try statement.");
        }
        final Assignment nullStat = new BinaryAssignment(exceptionVar, NullLiteral.NULL);
        final VariableSpecification eSpec = new VariableSpecification(eVar);
        final ParameterDeclaration excDecl =
            new ParameterDeclaration(new Modifier[0], excTypeRef, eSpec, false);
        final Assignment assignStat = new BinaryAssignment(exceptionVar, eVar);
        final Catch catchStat = new Catch(excDecl, new StatementBlock(assignStat));
        final Try tryStat = new Try(sb, new Branch[] { catchStat });
        final StatementBlock sb2 = new StatementBlock(nullStat, tryStat);

        // create java block
        return JavaBlock.createJavaBlock(sb2);
    }

    /**
     * Creates the method body statement for a non-constructor method call. The
     * context ({@code newContext}) and result ({@code res}) are deliberately
     * {@code null} for static and void methods respectively; the
     * {@code MethodBodyStatement} constructor tolerates this (neither is
     * dereferenced before being assigned, matching its usage throughout
     * key.core), but its parameters are not nullness annotated.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    private static MethodBodyStatement buildMethodBodyStatement(IProgramMethod method,
            @Nullable ProgramVariable newContext, @Nullable ProgramVariable res,
            ImmutableArray<Expression> args) {
        return new MethodBodyStatement(method, newContext, res, args);
    }


    private ProgramVariable[] extractProgramVariables(ImmutableList<JTerm> formalPars)
            throws IllegalArgumentException {
        ProgramVariable[] formalParVars = new ProgramVariable[formalPars.size()];
        int i = 0;
        for (JTerm formalPar : formalPars) {
            formalParVars[i++] = formalPar.op(ProgramVariable.class);
        }
        return formalParVars;
    }
}
