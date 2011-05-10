// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

/**
 * Sequence getter operation.
 * @author bruns
 * @since 1.7.2119
 */
public class SeqGet extends ADTPrefixConstruct {
    
    /**
     * Creates a sequence getter operator.
     * @param seq Sequence to operate on
     * @param idx Index position (from 0 to length-1)
     */
    public SeqGet(Expression seq, Expression idx) {
        super(seq, idx);
        makeParentRoleValid();
    }


    protected SeqGet(SeqGet proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override    
    public SeqGet deepClone() {
        return new SeqGet(this);
    }


    @Override    
    public int getArity() {
        return 2;
    }


    @Override    
    public int getNotation() {
        return POSTFIX;
    }
    
    @Override
    public String toSource(){
        return children.get(0).toSource()+"["+children.get(1).toSource()+"]";
    }
}
