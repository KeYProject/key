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

package de.uka.ilkd.key.java.recoderext;

import java.util.List;

import recoder.java.Expression;
import de.uka.ilkd.key.util.MiscTools;

/**
 * This class is used to parse function applications with JavaDL escapes within
 * set statements or similar situations.
 * 
 * 
 * @author Mattias Ulbrich
 */
public class DLEmbeddedExpression extends EscapeExpression {

    private static final long serialVersionUID = 1210489918296848261L;

    public DLEmbeddedExpression(String functionName, List<Expression> arguments) {
        super(functionName, arguments);
    }

    @Override
    public Expression deepClone() {
        return new DLEmbeddedExpression(functionName, children);
    }
    
    @Override
    public String toSource() {
        return "\\dl_" + functionName + "(" + MiscTools.join(children, ",") + ")";
    }

}