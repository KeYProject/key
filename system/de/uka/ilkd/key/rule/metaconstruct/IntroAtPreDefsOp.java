// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.IteratorOfLoopStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.SetAsListOfLoopStatement;
import de.uka.ilkd.key.java.statement.SetOfLoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;


/**
 * Creates an anonymising update for a modifies clause.
 */
public class IntroAtPreDefsOp extends AbstractMetaOperator {
    
    private static final AtPreFactory APF = AtPreFactory.INSTANCE;
   
    public IntroAtPreDefsOp() {
        super(new Name("#introAtPreDefs"), 1);
    }

    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        Term target = term.sub(0);
        
        //the target term should have a Java block 
        ProgramElement pe = target.javaBlock().program();
        assert pe != null;
                
        //collect all loops in the innermost method frame
        Object[] frameAndLoops = new JavaASTVisitor(pe, services) {
            private MethodFrame frame = null;
            private SetOfLoopStatement loops = SetAsListOfLoopStatement.EMPTY_SET;
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame && frame == null) {
                    frame = (MethodFrame) node;
                } else if(frame == null && node instanceof LoopStatement) {
                    loops = loops.add((LoopStatement) node);
                }
            }
            public Object[] run() {
                walk(root());
                return new Object[]{frame, loops};
            }
        }.run();
        MethodFrame frame = (MethodFrame) frameAndLoops[0];
        SetOfLoopStatement loops = (SetOfLoopStatement) frameAndLoops[1];
        
        //determine "self"
        Term selfTerm;
        ExecutionContext ec = (ExecutionContext) frame.getExecutionContext();
        ReferencePrefix rp = ec.getRuntimeInstance();
        if(rp == null || rp instanceof TypeReference) {
            selfTerm = null;
        } else {
            selfTerm = services.getTypeConverter().convertToLogicElement(rp);
        }

        //collect atPre-functions, update loop invariants
        Map<Operator, Function /*atPre*/> atPreFunctions = 
            new LinkedHashMap<Operator, Function>();
        for(IteratorOfLoopStatement it = loops.iterator(); it.hasNext(); ) {
            LoopStatement loop = it.next();
            LoopInvariant inv 
                = services.getSpecificationRepository().getLoopInvariant(loop);
            if(inv != null) {
                if(selfTerm != null && inv.getInternalSelfTerm() == null) {
                    //we're calling a static method from an instance context
                    selfTerm = null;
                }
                Term newInvariant 
                    = inv.getInvariant(selfTerm, atPreFunctions, services);
                SetOfTerm newPredicates
                    = inv.getPredicates(selfTerm, atPreFunctions, services);
                SetOfLocationDescriptor newModifies
                    = inv.getModifies(selfTerm, atPreFunctions, services);
                Term newVariant
                    = inv.getVariant(selfTerm, atPreFunctions, services);
                boolean newPredicateHeuristicsAllowed
                    = inv.getPredicateHeuristicsAllowed();
                
                LoopInvariant newInv 
                    = new LoopInvariantImpl(loop, 
                                            newInvariant, 
                                            newPredicates,
                                            newModifies, 
                                            newVariant, 
                                            selfTerm,
                                            atPreFunctions,
                                            newPredicateHeuristicsAllowed);
                services.getSpecificationRepository().setLoopInvariant(newInv);                
            }
        }
        
        //define atPre symbols
        UpdateFactory uf 
            = new UpdateFactory(services, services.getProof().simplifier());
        Update atPreUpdate 
            = APF.createAtPreDefinitions(atPreFunctions, services);
        return uf.apply(atPreUpdate, target);
    }
}
