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


package de.uka.ilkd.key.gui;

/**
 *  This is a handy class for tracing Exceptions that are otherwise lost in 
 *  the thread chaos. See the method handleException() in 
 *  class java.awt.EventDispatchThread. The magic system property 
 *  "sun.awt.exception.handler" must be set to 
 *  "de.uka.ilkd.key.gui.ExceptionalHandler" for this to work.
 */

public class ExceptionalHandler {

    public void handle(Throwable t) {
        System.err.println("*** Here's the exceptional handler ***");
        System.err.println(t);
        t.printStackTrace();
    }

}
