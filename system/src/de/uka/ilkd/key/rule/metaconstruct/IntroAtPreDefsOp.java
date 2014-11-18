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

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Triple;

public final class IntroAtPreDefsOp extends AbstractTermTransformer {

    public IntroAtPreDefsOp() {
        super(new Name("#introAtPreDefs"), 1);
    }


    @Override
    public Term transform(Term term,
                  SVInstantiations svInst,
                  Services services) {
        final TermBuilder TB = services.getTermBuilder();
        final Term target = term.sub(0);

        //the target term should have a Java block
        final ProgramElement pe = target.javaBlock().program();
        assert pe != null;

        //collect all loops in the innermost method frame
        final Triple<MethodFrame,
                     ImmutableSet<LoopStatement>,
                     ImmutableSet<StatementBlock>> frameAndLoopsAndBlocks =
              new JavaASTVisitor(pe, services) {
            private MethodFrame frame = null;
            private ImmutableSet<LoopStatement> loops
                = DefaultImmutableSet.<LoopStatement>nil();
            private ImmutableSet<StatementBlock> blocks
                = DefaultImmutableSet.nil();
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame && frame == null) {
                    frame = (MethodFrame) node;
                } else if(frame == null && node instanceof LoopStatement) {
                    loops = loops.add((LoopStatement) node);
                }
                else if (frame == null && node instanceof StatementBlock) {
                    blocks = blocks.add((StatementBlock) node);
                }
            }
            public Triple<MethodFrame,
                          ImmutableSet<LoopStatement>,
                          ImmutableSet<StatementBlock>> run() {
                walk(root());
                return new Triple<MethodFrame,
                                  ImmutableSet<LoopStatement>,
                                  ImmutableSet<StatementBlock>>(
                        frame, loops, blocks);
            }
        }.run();
        final MethodFrame frame = frameAndLoopsAndBlocks.first;
        final ImmutableSet<LoopStatement> loops = frameAndLoopsAndBlocks.second;

        //determine "self"
        Term selfTerm;
        final ExecutionContext ec
            = (ExecutionContext) frame.getExecutionContext();
        final ReferencePrefix rp = ec.getRuntimeInstance();
        if(rp == null || rp instanceof TypeReference) {
            selfTerm = null;
        } else {
            selfTerm = services.getTypeConverter().convertToLogicElement(rp);
        }

        //create atPre heap
        final String methodName = frame.getProgramMethod().getName();

        Term atPreUpdate = null;
        Map<LocationVariable,Term> atPres = new LinkedHashMap<LocationVariable,Term>();
        Map<LocationVariable,LocationVariable> atPreVars = new LinkedHashMap<LocationVariable, LocationVariable>();
        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps(services)) {
          final LocationVariable l = TB.heapAtPreVar(heap.name()+"Before_" + methodName, heap.sort(), true);
          // buf fix. see #1197
          services.getNamespaces().programVariables().addSafely(l);
          final Term u = TB.elementary(l, TB.var(heap));
          if(atPreUpdate == null) {
             atPreUpdate =u;
          }else{
             atPreUpdate = TB.parallel(atPreUpdate, u);
          }
          atPres.put(heap, TB.var(l));
          atPreVars.put(heap, l);
        }

        //update loop invariants
        for(LoopStatement loop : loops) {
            LoopInvariant inv
                = services.getSpecificationRepository().getLoopInvariant(loop);
            if(inv != null) {
                if(selfTerm != null && inv.getInternalSelfTerm() == null) {
                    //we're calling a static method from an instance context
                    selfTerm = null;
                }

                final Term newVariant
                    = inv.getVariant(selfTerm, atPres, services);

                Map<LocationVariable,Term> newMods = new LinkedHashMap<LocationVariable,Term>();
                Map<LocationVariable,
                    ImmutableList<InfFlowSpec>> newInfFlowSpecs
                                 = new LinkedHashMap<LocationVariable,
                                                     ImmutableList<InfFlowSpec>>();
                //LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
                Map<LocationVariable,Term> newInvariants = new LinkedHashMap<LocationVariable,Term>();
                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps(services)) {
                  if(heap == services.getTypeConverter().getHeapLDT().getSavedHeap()
                     &&
                     inv.getInternalModifies().get(services.getTypeConverter().getHeapLDT().getHeap()).equals(TB.strictlyNothing())) {
                    continue;
                  }
                  final Term m = inv.getModifies(heap, selfTerm, atPres, services);
                  final ImmutableList<InfFlowSpec> infFlowSpecs =
                                 inv.getInfFlowSpecs(heap, selfTerm, atPres, services);
                  final Term i = inv.getInvariant(heap, selfTerm, atPres, services);
                  if(m != null) { newMods.put(heap, m); }
                  newInfFlowSpecs.put(heap, infFlowSpecs);
                  if(i != null) { newInvariants.put(heap, i); }
                }
                ImmutableList<Term> newLocalIns = TB.var(MiscTools.getLocalIns(loop, services));
                ImmutableList<Term> newLocalOuts = TB.var(MiscTools.getLocalOuts(loop, services));
                final LoopInvariant newInv
                       = inv.create(loop,
                                    frame.getProgramMethod(),
                                    frame.getProgramMethod().getContainerType(),
                                    newInvariants,
                                    newMods,
                                    newInfFlowSpecs,
                                    newVariant,
                                    selfTerm,
                                    newLocalIns,
                                    newLocalOuts,
                                    atPres);
                services.getSpecificationRepository().addLoopInvariant(newInv);
            }
        }

        /*//update block contracts
        for (StatementBlock block : blocks) {
            ImmutableSet<BlockContract> contracts =
                    services.getSpecificationRepository().getBlockContracts(block);
            for (BlockContract contract : contracts) {
                final BlockContract.Variables variables = contract.getPlaceholderVariables();
                final BlockContract.Variables newVariables = new BlockContract.Variables(
                        variables.self,
                        variables.breakFlags,
                        variables.continueFlags,
                        variables.returnFlag,
                        variables.result,
                        variables.exception,
                        atPreVars,
                        variables.remembranceLocalVariables
                );
                final Map<LocationVariable, Term> newPreconditions =
                        new LinkedHashMap<LocationVariable, Term>();
                final Map<LocationVariable, Term> newPostconditions =
                        new LinkedHashMap<LocationVariable, Term>();
                final Map<LocationVariable, Term> newModifiesClauses =
                        new LinkedHashMap<LocationVariable, Term>();
                ImmutableList<Triple<ImmutableList<Term>,
                                     ImmutableList<Term>,
                                     ImmutableList<Term>>> newRespectsClause =
                        ImmutableSLList.<Triple<ImmutableList<Term>,
                                                ImmutableList<Term>,
                                                ImmutableList<Term>>>nil();
                for (LocationVariable heap : HeapContext.getModHeaps(services, transaction)) {
                    newPreconditions.put(heap,
                                         contract.getPrecondition(heap, newVariables.self,
                                                                  atPreVars, services));
                    newPostconditions.put(heap,
                                          contract.getPostcondition(heap, newVariables, services));
                    newModifiesClauses.put(heap,
                                           contract.getModifiesClause(heap, newVariables.self,
                                                                      services));
                    newRespectsClause = contract.getRespectsClause(newVariables.self,
                                                                   services);
                }
                final BlockContract newBlockContract =
                        contract.update(block, newPreconditions, newPostconditions,
                                        newModifiesClauses, newRespectsClause, newVariables);
                services.getSpecificationRepository().addBlockContract(newBlockContract);
            }
        }*/

        return TB.apply(atPreUpdate, target, null);
    }
}
