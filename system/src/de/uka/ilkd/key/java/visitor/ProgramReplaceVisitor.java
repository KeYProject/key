// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/** 
 * Walks through a java AST in depth-left-fist-order. 
 * This walker is used to transform a program according to the given 
 * SVInstantiations.
 */
public class ProgramReplaceVisitor extends CreatingASTVisitor {


    private ProgramElement result = null;

    private SVInstantiations svinsts;

    private boolean allowPartialReplacement;

    /** 
     * create the  ProgramReplaceVisitor
     * @param root the ProgramElement where to begin
     */
    public ProgramReplaceVisitor(ProgramElement root,
				 Services services, 
				 SVInstantiations svi,
				 boolean allowPartialReplacement) {
	super(root, false, services);
	svinsts = svi;
	this.allowPartialReplacement=allowPartialReplacement;
    }

    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected void doAction(ProgramElement node) {
	node.visit(this);
    }
    
    /** starts the walker*/
    public void start() {	
	stack.push(new ExtList());		
	walk(root());
	final ExtList el = stack.peek();
	int i = 0;
	while (!(el.get(i) instanceof ProgramElement)) {
	    i++;
	}
	result = (ProgramElement) (stack.peek()).get(i);
    }

    public ProgramElement result() { 	
	return result;
    }
    
    public String toString() {
	return stack.peek().toString();
    }

    /** the implemented default action is called if a program element is,
     * and if it has children all its children too are left unchanged
     */
    protected void doDefaultAction(SourceElement x) {
	addChild(x);
    }

    public void performActionOnSchemaVariable(SchemaVariable sv) {
	final Object inst = svinsts.getInstantiation(sv);
	if (inst instanceof ProgramElement) {
	    Debug.out("ProgramReplace SV:", sv);
	    Debug.out("ProgramReplace:", inst);
	    addChild((ProgramElement)inst);
	} else if (inst instanceof ImmutableArray/*<ProgramElement>*/) {
	    final ImmutableArray<ProgramElement> instArray = (ImmutableArray<ProgramElement>)inst;
	    // the assertion ensures the intended instanceof check from above
	    assert instArray.size() == 0 || instArray.last() instanceof ProgramElement;
	    addChildren(instArray);
	} else if (inst instanceof Term
		   && ((Term)inst).op() instanceof ProgramInLogic) {
	    addChild(services.getTypeConverter().convertToProgramElement((Term)inst));
	} else {
	    if ( inst == null && allowPartialReplacement &&
		 sv instanceof SourceElement ) {
		doDefaultAction ( (SourceElement)sv );
		return;
	    }
	    Debug.fail("programreplacevisitor: Instantiation missing " + 
		       "for schema variable ", sv);
	}
	changed();
    }


    public void performActionOnProgramMetaConstruct(ProgramTransformer x) {
	ProgramReplaceVisitor trans = new ProgramReplaceVisitor(x.body(), services,
								svinsts,
								allowPartialReplacement);
	trans.start();
	ProgramElement localresult = trans.result();
	localresult = x.transform(localresult, services, svinsts);
	addChild(localresult);
	changed();
    }

    public void performActionOnAbstractProgramElement(AbstractProgramElement x) {
	result = x.getConcreteProgramElement(services);
	addChild(result);
	changed();
    }
}
