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



package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  For.
 *  
 */

public class For extends LoopStatement implements VariableScope {

    private static final 
    ImmutableArray<VariableSpecification> EMPTY_VARSPECS=
    new ImmutableArray<VariableSpecification>(new VariableSpecification[0]);

    /**
     *      For.
     */
    public For() {}

    /**
     *      For. Used for the Recoder2KeY transformation
     *      @param inits a loop initializer mutable list.
     *      @param guard an expression.
     *      @param updates an expression mutable list.
     *      @param body a statement.
     */
    public For(LoopInitializer[] inits, Expression guard,
               Expression[] updates, Statement body) {	
        super(inits, guard, updates, body);
    }

    public For(ILoopInit inits, IGuard guard,
               IForUpdates updates, Statement body, ExtList comments) {	
        super(inits, guard, updates, body, comments);
    }

    public For(ILoopInit inits, IGuard guard,
               IForUpdates updates, Statement body, 
	       ExtList comments, PositionInfo pos) {	
        super(inits, guard, updates, body, comments, pos);
    }

    public For(ILoopInit inits, IGuard guard,
               IForUpdates updates, Statement body) {	
        super(inits, guard, updates, body);
    }

    public For(ExtList children) {
	super(children.get(ILoopInit.class), 
	      children.get(IGuard.class),
	      children.get(IForUpdates.class),
	      children.get(Statement.class),
	      children);
    }

    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     *      Is checked before iteration.
     *      @return the boolean value.
     */

    public boolean isCheckedBeforeIteration() {
        return true;
    }

    public boolean isDefinedScope() {
        return true;
    }

    public ImmutableArray<VariableSpecification> getVariablesInScope() {
        if (inits != null) {
            LoopInitializer li = inits.getInits().get(0);
            if (li instanceof LocalVariableDeclaration) {
                return ((LocalVariableDeclaration)li).getVariables();
            }
        }
        return EMPTY_VARSPECS;
    }

    public VariableSpecification getVariableInScope(String name) {
        if (inits != null) {
            LoopInitializer li = inits.getInits().get(0);
            if (li instanceof LocalVariableDeclaration) {
                ImmutableArray<VariableSpecification> vars =
                    ((LocalVariableDeclaration)li).getVariables();
                for (int i = 0, s = vars.size(); i < s; i += 1) {
                    VariableSpecification v = vars.get(i);
                    if (name.equals(v.getName())) {
                        return v;
                    }
                }
            }
        }
        return null;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnFor(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printFor(this);
    }

}
