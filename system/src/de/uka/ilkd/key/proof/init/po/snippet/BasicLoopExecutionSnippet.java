package de.uka.ilkd.key.proof.init.po.snippet;

import java.util.Iterator;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
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
        if (poVars.selfAtPost != null)
            posts = posts.append(d.tb.equals(poVars.selfAtPost, poVars.self));

        if (poVars.guard != null) {
            final JavaBlock guardJb = buildJavaBlock(d).second;
            posts = posts.append(d.tb.box(guardJb,
                                          d.tb.equals(poVars.guardAtPost,
                                                      d.origVars.guard)));
        }
        Iterator<Term> out = poVars.localOuts.iterator();
        Iterator<Term> in = d.origVars.localIns.iterator();
        while (in.hasNext()) {
            Term i = in.next();
            Term o = out.next();
            if (i != null && o != null)
                posts = posts.append(d.tb.equals(o, i));
        }
        posts = posts.append(d.tb.equals(poVars.heapAtPost, d.tb.getBaseHeap()));
        
        return buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
    }

    private Term buildProgramTerm(BasicSnippetData d,
                                  ProofObligationVars vs,
                                  Term postTerm,
                                  TermBuilder.Serviced tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException("Tried to produce a " +
                                                    "program-term for a loop without modality.");
        }
        LoopInvariant inv = (LoopInvariant) d.get(BasicSnippetData.Key.LOOP_INVARIANT);
        Services services = d.tb.getServices();

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
        final Term guardTrueTerm = d.tb.equals(d.tb.var((LocationVariable) inv.getGuard().op()), 
                                               d.tb.TRUE(services));
        final Term guardFalseTerm = d.tb.equals(d.tb.var((LocationVariable) inv.getGuard().op()), 
                d.tb.FALSE(services));
        final Term bodyTerm = tb.prog(symbExecMod, jb.first, postTerm);
        final Term guardTrueBody =
                d.tb.imp(tb.prog(modality, jb.second, guardTrueTerm),
                         bodyTerm);
        final Term guardFalseBody =
                d.tb.imp(tb.prog(modality, jb.second, guardFalseTerm),
                         postTerm);
        final Term programTerm = d.tb.and(guardTrueBody, guardFalseBody);

        //create update
        Term update = tb.skip();
        Iterator<Term> paramIt = vs.localIns.iterator();
        Iterator<Term> origParamIt = d.origVars.localIns.iterator();
        while (paramIt.hasNext()) {
            Term paramUpdate =
                    d.tb.elementary(d.tb.getServices(), origParamIt.next(), paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }
        return tb.apply(update, programTerm);
    }

    private Pair<JavaBlock, JavaBlock> buildJavaBlock(BasicSnippetData d) {
        Services services = d.tb.getServices();
        final KeYJavaType booleanKJT = services.getTypeConverter().getBooleanType();
        ExecutionContext context =
                (ExecutionContext) d.get(BasicSnippetData.Key.CONTEXT);        

        //create loop call
        LoopInvariant inv = (LoopInvariant) d.get(BasicSnippetData.Key.LOOP_INVARIANT);
        StatementBlock sb = (StatementBlock) inv.getLoop().getBody();

        final VariableSpecification guardVarSpec 
        = new VariableSpecification((LocationVariable) inv.getGuard().op(), 
                                    inv.getLoop().getGuardExpression(), 
                                    booleanKJT);
        final LocalVariableDeclaration guardVarDecl 
        = new LocalVariableDeclaration(new TypeRef(booleanKJT), 
                guardVarSpec);
        final Statement guardVarMethodFrame 
        = context == null 
        ? guardVarDecl
                : new MethodFrame(null, 
                        context,
                        new StatementBlock(guardVarDecl));

        //create java block
        final JavaBlock guardJb
        = JavaBlock.createJavaBlock(new StatementBlock(guardVarMethodFrame));
        final Statement s = new MethodFrame(null, context, sb);
        final JavaBlock res = JavaBlock.createJavaBlock(new StatementBlock(s));

        return new Pair<JavaBlock, JavaBlock>(res, guardJb);
    }
}