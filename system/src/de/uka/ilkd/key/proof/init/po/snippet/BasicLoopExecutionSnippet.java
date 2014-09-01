package de.uka.ilkd.key.proof.init.po.snippet;

import java.util.Iterator;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.Pair;

public class BasicLoopExecutionSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        ImmutableList<Term> posts = ImmutableSLList.<Term>nil();
        if (poVars.post.self != null)
            posts = posts.append(d.tb.equals(poVars.post.self, poVars.pre.self));

        if (poVars.pre.guard != null) {
            final JavaBlock guardJb = buildJavaBlock(d).second;
            posts = posts.append(d.tb.box(guardJb,
                                          d.tb.equals(poVars.post.guard,
                                                      d.origVars.guard)));
        }
        Iterator<Term> localVars = d.origVars.localVars.iterator();
        Iterator<Term> localVarsAtPost = poVars.post.localVars.iterator();
        while (localVars.hasNext()) {
            Term i = localVars.next();
            Term o = localVarsAtPost.next();
            if (i != null && o != null)
                posts = posts.append(d.tb.equals(o, i));
        }
        posts = posts.append(d.tb.equals(poVars.post.heap, d.tb.getBaseHeap()));
        
        return buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
    }

    private Term buildProgramTerm(BasicSnippetData d,
                                  ProofObligationVars vs,
                                  Term postTerm,
                                  TermBuilder tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException("Tried to produce a " +
                                                    "program-term for a loop without modality.");
        }
        //create java block
        Modality modality =
                (Modality) d.get(BasicSnippetData.Key.MODALITY);
        final Pair<JavaBlock, JavaBlock> jb = buildJavaBlock(d);

        //create program term
        final Modality symbExecMod;
        if (modality == Modality.BOX) {
            symbExecMod = Modality.DIA;
        } else {
            symbExecMod = Modality.BOX;
        }
        final Term guardPreTrueTerm = d.tb.equals(vs.pre.guard,
                                                  d.tb.TRUE());
        final Term guardPreFalseTerm = d.tb.equals(vs.pre.guard,
                                                   d.tb.FALSE());
        final Term guardPreEqTerm = d.tb.equals(d.origVars.guard,
                                                vs.pre.guard);
        final Term guardPreTerm = tb.prog(modality, jb.second, guardPreEqTerm);
        final Term bodyTerm = tb.prog(symbExecMod, jb.first, postTerm);
        final Term guardTrueBody = d.tb.imp(guardPreTrueTerm, bodyTerm);
        final Term guardFalseBody = d.tb.imp(guardPreFalseTerm, postTerm);
        final Term programTerm = d.tb.and(guardPreTerm, guardTrueBody, guardFalseBody);

        //create update
        Term update = tb.skip();
        Iterator<Term> paramIt = vs.pre.localVars.iterator();
        Iterator<Term> origParamIt = d.origVars.localVars.iterator();
        while (paramIt.hasNext()) {
            Term paramUpdate =
                    d.tb.elementary(origParamIt.next(), paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }
        if (vs.post.self != null) {
            Term selfUpdate =
                    d.tb.elementary(d.origVars.self, vs.pre.self);
            update = tb.parallel(selfUpdate, update);
        }
        return tb.apply(update, programTerm);
    }

    private Pair<JavaBlock, JavaBlock> buildJavaBlock(BasicSnippetData d) {
        ExecutionContext context =
                (ExecutionContext) d.get(BasicSnippetData.Key.EXECUTION_CONTEXT);        

        //create loop call
        LoopInvariant inv = (LoopInvariant) d.get(BasicSnippetData.Key.LOOP_INVARIANT);
        StatementBlock sb = (StatementBlock) inv.getLoop().getBody();

        final Assignment guardVarDecl =
                new CopyAssignment((LocationVariable)d.origVars.guard.op(),
                                   inv.getLoop().getGuardExpression());
        final Statement guardVarMethodFrame =
                context == null ?
                        guardVarDecl : new MethodFrame(null, context,
                                                       new StatementBlock(guardVarDecl));

        //create java block
        final JavaBlock guardJb =
                JavaBlock.createJavaBlock(new StatementBlock(guardVarMethodFrame));
        final Statement s = new MethodFrame(null, context, sb);
        final JavaBlock res = JavaBlock.createJavaBlock(new StatementBlock(s));

        return new Pair<JavaBlock, JavaBlock>(res, guardJb);
    }
}