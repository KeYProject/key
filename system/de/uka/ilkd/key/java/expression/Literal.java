// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.expression;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Literal.
 *  @author <TT>AutoDoc</TT>
 */

public abstract class Literal extends JavaProgramElement implements Expression, TerminalProgramElement {


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     *     May contain: Comments
     */
    public Literal(ExtList children) {
	super(children);
    }

    /**
     * Literal
     */
    public Literal() {
	
    }

    /** retrieves the literal's type (as it is independant of the
     * execution context, it is same as using {@link #getKeYJavaType(Services)})
     * @param javaServ the Services offering access to the Java model 
     * @param ec the ExecutionContext in which the expression is evaluated 
     * @return the literal's type
     */
    public KeYJavaType getKeYJavaType(Services javaServ, 
				      ExecutionContext ec) {
	return getKeYJavaType(javaServ);
    }
    
    /** retrieves the literal's type 
     * @param javaServ the Services offering access to the Java model 
     * @return the literal's type
     */
    public abstract KeYJavaType getKeYJavaType(Services javaServ);
    
    
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if (this.equals(src)) {
            source.next();
            return matchCond;
        } else {
            Debug.out("Program match failed (pattern, source)", this, src);
            return null;
        }        
    }

}
