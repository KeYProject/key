// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.util.Pair;

public final class IntroAtPreDefsOp extends AbstractTermTransformer {
          
    public IntroAtPreDefsOp() {
        super(new Name("#introAtPreDefs"), 1);
    }

    
    @Override
    public Term transform(Term term, 
	    		  SVInstantiations svInst, 
	    		  Services services) {
        final Term target = term.sub(0);
        final boolean transaction =
              (target.op() != null &&
                  (target.op() == Modality.DIA_TRANSACTION || target.op() == Modality.BOX_TRANSACTION));
        final HeapContext hc = transaction ? HeapContext.LOOP_TR_HC : HeapContext.LOOP_HC;
        
        //the target term should have a Java block 
        final ProgramElement pe = target.javaBlock().program();
        assert pe != null;
                
        //collect all loops in the innermost method frame
        final Pair<MethodFrame,ImmutableSet<LoopStatement>> frameAndLoops 
        	= new JavaASTVisitor(pe, services) {
            private MethodFrame frame = null;
            private ImmutableSet<LoopStatement> loops 
            	= DefaultImmutableSet.<LoopStatement>nil();
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame && frame == null) {
                    frame = (MethodFrame) node;
                } else if(frame == null && node instanceof LoopStatement) {
                    loops = loops.add((LoopStatement) node);
                }
            }
            public Pair<MethodFrame,ImmutableSet<LoopStatement>> run() {
                walk(root());
                return new Pair<MethodFrame,ImmutableSet<LoopStatement>>(frame, loops);
            }
        }.run();
        final MethodFrame frame = frameAndLoops.first;
        final ImmutableSet<LoopStatement> loops = frameAndLoops.second;
        
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
        for(LocationVariable heap : hc.getModHeaps(services)) {
          final LocationVariable l = TB.heapAtPreVar(services, heap.name()+"Before_" + methodName, true);
          final Term u = TB.elementary(services,
            l,
            TB.var(heap));
          if(atPreUpdate == null) {
             atPreUpdate =u;
          }else{
             atPreUpdate = TB.parallel(atPreUpdate, u);
          }
          atPres.put(heap, TB.var(l));
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
                final Term newTransactionInvariant =
                  transaction ?
                     inv.getInvariant(selfTerm, atPres, services, true)
                   : null;

                final Term newInvariant 
                    = inv.getInvariant(selfTerm, atPres, services, false);
                final Term newVariant
                    = inv.getVariant(selfTerm, atPres, services);

                Map<LocationVariable,Term> newMods = new LinkedHashMap<LocationVariable,Term>();
                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                  final Term m = inv.getModifies(heap, selfTerm, atPres, services);
                  newMods.put(heap, m);
                }
                final LoopInvariant newInv 
             	       = new LoopInvariantImpl(loop, 
                                            newInvariant,
                                            newTransactionInvariant,
                                            newMods, 
                                            newVariant, 
                                            selfTerm,
                                            atPres);
                services.getSpecificationRepository().setLoopInvariant(newInv);                
            }
        }
        hc.reset();
        return TB.apply(atPreUpdate, target);
    }
}
