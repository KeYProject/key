// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.speclang.LoopPredicateSet;
import de.uka.ilkd.key.util.InvInferenceTools;
import de.uka.ilkd.key.util.Pair;



public final class IntroAtPreDefsOp extends AbstractMetaOperator {
    
    private static final InvInferenceTools IIT 
    	= InvInferenceTools.INSTANCE;
       
    public IntroAtPreDefsOp() {
        super(new Name("#introAtPreDefs"), 1);
    }

    
    @Override
    public Term calculate(Term term, 
	    		  SVInstantiations svInst, 
	    		  Services services) {
        final Term target = term.sub(0);
        
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
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final String methodName = frame.getProgramMethod().getName();
	final ProgramElementName heapBeforeLoopName 
		= new ProgramElementName(IIT.getNewName("heapBefore_" + methodName, 
							services));
	final LocationVariable heapAtPreVar 
		= new LocationVariable(heapBeforeLoopName,
				       new KeYJavaType(heapLDT.targetSort()));
	services.getNamespaces().programVariables().addSafely(heapAtPreVar);
	final Term heapAtPre = TB.var(heapAtPreVar);
	final Term heapAtPreUpdate = TB.elementary(services, 
						   heapAtPreVar, 
						   TB.heap(services));
        
        //collect atPre-functions, update loop invariants
        Map<Operator, Function /*atPre*/> atPreFunctions = 
            new LinkedHashMap<Operator, Function>();
        for(LoopStatement loop : loops) {
            LoopInvariant inv 
                = services.getSpecificationRepository().getLoopInvariant(loop);
            if(inv != null) {
                if(selfTerm != null && inv.getInternalSelfTerm() == null) {
                    //we're calling a static method from an instance context
                    selfTerm = null;
                }
                final Term newInvariant 
                    = inv.getInvariant(selfTerm, heapAtPre, services);
                final LoopPredicateSet newPredicates
                    = inv.getPredicates(selfTerm, heapAtPre, services);
                final Term newModifies
                    = inv.getModifies(selfTerm, heapAtPre, services);
                final Term newVariant
                    = inv.getVariant(selfTerm, heapAtPre, services);
                boolean newPredicateHeuristicsAllowed
                    = inv.getPredicateHeuristicsAllowed();
                
                final LoopInvariant newInv 
                    = new LoopInvariantImpl(loop, 
                                            newInvariant, 
                                            newPredicates,
                                            newModifies, 
                                            newVariant, 
                                            selfTerm,
                                            heapAtPre,
                                            newPredicateHeuristicsAllowed);
                services.getSpecificationRepository().setLoopInvariant(newInv);                
            }
        }
        
        return TB.apply(heapAtPreUpdate, target);
    }
}
