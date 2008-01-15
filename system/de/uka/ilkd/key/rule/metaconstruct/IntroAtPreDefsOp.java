// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.IteratorOfLoopStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.SetAsListOfLoopStatement;
import de.uka.ilkd.key.java.statement.SetOfLoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.LoopInvariant;


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
        SetOfLoopStatement loops = new JavaASTVisitor(pe, services) {
            private SetOfLoopStatement result = SetAsListOfLoopStatement.EMPTY_SET;
            private boolean done = false;
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame) {
                    done = true;
                } else if(node instanceof LoopStatement && !done) {
                    result = result.add((LoopStatement) node);
                }
            }
            public SetOfLoopStatement run() {
                walk(root());
                return result;
            }
        }.run();
        
        //create update defining all atPre symbols used in these loops
        UpdateFactory uf = new UpdateFactory(services, 
                                             services.getProof().simplifier());
        Update atPreUpdate = uf.skip();
        IteratorOfLoopStatement it = loops.iterator();
        while(it.hasNext()) {
            LoopStatement loop = it.next();
            LoopInvariant inv = services.getSpecificationRepository()
                                        .getLoopInvariant(loop);
            if(inv != null) {
                Update u = APF.createAtPreDefinitions(inv.getAtPreFunctions(), 
                                                      services);                
                atPreUpdate = uf.parallel(atPreUpdate, u);
            }
        }
        
        return uf.apply(atPreUpdate, target);
    }
}
