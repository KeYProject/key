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

package de.uka.ilkd.key.java.visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;

/** 
 * Walks through a java AST in depth-left-fist-order. 
 * This walker is used to transform a program according to the given 
 * SVInstantiations.
 */
public class ProgramReplaceVisitor extends CreatingASTVisitor {

    private ProgramElement result = null;

    private final SVInstantiations svinsts;
    
    /** 
     * create the  ProgramReplaceVisitor
     * @param root the ProgramElement where to begin
     */
    public ProgramReplaceVisitor(ProgramElement root,
				 Services services, 
				 SVInstantiations svi) {
	super(root, false, services);
	svinsts = svi;
    }

    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected void doAction(ProgramElement node) {
	node.visit(this);
    }
    
    /** starts the walker*/
    public void start() {
    assert result == null : "ProgramReplaceVisitor is not designed for multiple walks";
	stack.push(new ExtList());		
	walk(root());
	final ExtList astList = stack.pop();
	for (int i = 0, sz = astList.size(); result == null && i<sz; i++) {	
	   final Object element = astList.get(i);
	   if (element instanceof ProgramElement) {
	       result = (ProgramElement) element;
	   }
	}
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
	    addChild((ProgramElement)inst);
	} else if (inst instanceof ImmutableArray/*<ProgramElement>*/) {
	    @SuppressWarnings("unchecked")
        final ImmutableArray<ProgramElement> instArray = (ImmutableArray<ProgramElement>)inst;        
	    // the assertion ensures the intended instanceof check from above
	    assert instArray.size() == 0 || instArray.last() instanceof ProgramElement;
	    addChildren(instArray);
	} else if (inst instanceof Term
		   && ((Term)inst).op() instanceof ProgramInLogic) {
	    addChild(services.getTypeConverter().convertToProgramElement((Term)inst));
	} else {
	    throw new IllegalStateException("programreplacevisitor: Instantiation missing " + 
		       "for schema variable " + sv);
	}
	changed();
    }

    public void performActionOnProgramMetaConstruct(ProgramTransformer x) {
	final ExtList changeList = stack.peek();
	
	ProgramElement body = null;
	for (Object element : changeList) {
	    if (element instanceof SourceElement) {
	        body = (ProgramElement) element;
	    }
	}

	assert body != null : "A program transformer without program to transform?";

	addChild(x.transform(body, services, svinsts));
	changed();
    }

    public void performActionOnAbstractProgramElement(AbstractProgramElement x) {
	addChild(x.getConcreteProgramElement(services));
	changed();
    }
}
