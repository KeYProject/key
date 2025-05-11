/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.Iterator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 *
 * @author christoph
 */
class BasicSymbolicExecutionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public @NonNull Term produce(@NonNull BasicSnippetData d, @NonNull ProofObligationVars poVars)
            throws UnsupportedOperationException {
        assert poVars.exceptionParameter.op() instanceof LocationVariable
                : "Something is wrong with the catch variable";

        ImmutableList<Term> posts = ImmutableSLList.nil();
        if (poVars.post.self != null) {
            posts = posts.append(d.tb.equals(poVars.post.self, poVars.pre.self));
        }
        if (poVars.post.resultTerm != null) {
            posts = posts.append(d.tb.equals(poVars.post.resultTerm, poVars.pre.resultTerm));
        }
        posts = posts.append(d.tb.equals(poVars.post.exception, poVars.pre.exception));
        posts = posts.append(d.tb.equals(poVars.post.heap, d.tb.getBaseHeap()));
        final Term prog = buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
        return prog;
    }

    private @NonNull Term buildProgramTerm(@NonNull BasicSnippetData d, @NonNull ProofObligationVars vs, @NonNull Term postTerm,
                                           @NonNull TermBuilder tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "program-term for a contract without modality.");
        }
        assert Modality.JavaModalityKind.class.equals(BasicSnippetData.Key.MODALITY.getType());
        Modality.JavaModalityKind kind =
            (Modality.JavaModalityKind) d.get(BasicSnippetData.Key.MODALITY);


        // create java block
        final JavaBlock jb = buildJavaBlock(d, vs.formalParams,
            vs.pre.self != null ? vs.pre.self.op(ProgramVariable.class) : null,
            vs.pre.resultTerm != null ? vs.pre.resultTerm.op(ProgramVariable.class) : null,
            vs.pre.exception != null ? vs.pre.exception.op(ProgramVariable.class) : null,
            vs.exceptionParameter.op(LocationVariable.class));

        // create program term
        final Modality.JavaModalityKind symbExecMod;
        if (kind == Modality.JavaModalityKind.BOX) {
            symbExecMod = Modality.JavaModalityKind.DIA;
        } else {
            symbExecMod = Modality.JavaModalityKind.BOX;
        }
        final Term programTerm = tb.prog(symbExecMod, jb, postTerm);
        // final Term programTerm = tb.not(tb.prog(modality, jb, tb.not(postTerm)));

        // create update
        Term update = tb.skip();
        Iterator<Term> formalParamIt = vs.formalParams.iterator();
        Iterator<Term> paramIt = vs.pre.localVars.iterator();
        while (formalParamIt.hasNext()) {
            Term formalParam = formalParamIt.next();
            LocationVariable formalParamVar = formalParam.op(LocationVariable.class);
            Term paramUpdate = tb.elementary(formalParamVar, paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }

        return tb.apply(update, programTerm);
    }

    private @NonNull JavaBlock buildJavaBlock(@NonNull BasicSnippetData d, @NonNull ImmutableList<Term> formalPars,
                                              @NonNull ProgramVariable selfVar, @Nullable ProgramVariable resultVar, @NonNull ProgramVariable exceptionVar,
                                              @NonNull LocationVariable eVar) {
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
            assert selfVar != null;
            assert resultVar == null;
            final Expression[] formalArray2 =
                formalArray.toArray(new Expression[formalArray.size()]);
            KeYJavaType forClass = (KeYJavaType) d.get(BasicSnippetData.Key.FOR_CLASS);
            final New n = new New(formalArray2, new TypeRef(forClass), null);
            final CopyAssignment ca = new CopyAssignment(selfVar, n);
            sb = new StatementBlock(ca);
        } else {
            final MethodBodyStatement call =
                new MethodBodyStatement(pm, selfVar, resultVar, formalArray);
            sb = new StatementBlock(call);
        }

        // type of the variable for the try statement
        final KeYJavaType eType = javaInfo.getTypeByClassName("java.lang.Throwable");
        final TypeReference excTypeRef = javaInfo.createTypeReference(eType);

        // create try statement
        final CopyAssignment nullStat = new CopyAssignment(exceptionVar, NullLiteral.NULL);
        final VariableSpecification eSpec = new VariableSpecification(eVar);
        final ParameterDeclaration excDecl =
            new ParameterDeclaration(new Modifier[0], excTypeRef, eSpec, false);
        final CopyAssignment assignStat = new CopyAssignment(exceptionVar, eVar);
        final Catch catchStat = new Catch(excDecl, new StatementBlock(assignStat));
        final Try tryStat = new Try(sb, new Branch[] { catchStat });
        final StatementBlock sb2 = new StatementBlock(nullStat, tryStat);

        // create java block
        JavaBlock result = JavaBlock.createJavaBlock(sb2);

        return result;
    }


    private ProgramVariable @NonNull [] extractProgramVariables(@NonNull ImmutableList<Term> formalPars)
            throws IllegalArgumentException {
        ProgramVariable[] formalParVars = new ProgramVariable[formalPars.size()];
        int i = 0;
        for (Term formalPar : formalPars) {
            formalParVars[i++] = formalPar.op(ProgramVariable.class);
        }
        return formalParVars;
    }
}
