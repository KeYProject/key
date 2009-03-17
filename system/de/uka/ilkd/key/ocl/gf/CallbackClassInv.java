// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//Copyright (c) Kristofer Johanisson 2004, Hans-Joachim Daniels 2005
//
//This program is free software; you can redistribute it and/or modify
//it under the terms of the GNU General Public License as published by
//the Free Software Foundation; either version 2 of the License, or
//(at your option) any later version.
//
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU General Public License for more details.
//
//You can either finde the file LICENSE or LICENSE.TXT in the source 
//distribution or in the .jar file of this application


package de.uka.ilkd.key.ocl.gf;

import java.util.logging.Level;

import de.uka.ilkd.key.casetool.UMLModelClass;

/** 
 * provides a interface for letting the GF editor send class invariants back to KeY
 * @author Kristofer Johannisson & Hans-Joachim Daniels 
 */
public class CallbackClassInv extends ConstraintCallback{
        boolean useTJC;
        Object tjc; 
        UMLModelClass rmc;
        /**
         * send invariant to Together using methods in ReprModelClass 
         */
        public CallbackClassInv(UMLModelClass rmc) {
                this.rmc = rmc;
                useTJC = false;
        }

        /**
         * calls the right methods to save the OCL constraints as JavaDocComments
         * @param invOCL the OCL constraint
         */
        public void sendConstraint(String invOCL) {
                if (logger.isLoggable(Level.FINE)) {
                        logger.fine("CallbackClassInv received OCL: " + invOCL);
                }
                final int invStart = invOCL.indexOf("inv:") + 4;
                final String toSend = invOCL.substring(invStart);
                if (logger.isLoggable(Level.FINE)) {
                        logger.fine("invariant: " + toSend);
                }
                // pass inv on to KeY                
                rmc.setMyInv(toSend);
                rmc.setMyInvGFAbs(null); //delete that JavaDoc comment
        }
        
        /**
         * calls the right methods to save the unfinished OCL constrain
         * as JavaDocComments in GF tree syntax
         * @param abs the GF AST
         */
        public void sendAbstract(String abs) {
                if (logger.isLoggable(Level.FINE)) {
                        logger.fine("CallbackClassInv received Abstract: " + abs);
                }
                // pass inv on to KeY
                rmc.setMyInv(null); //delete that JavaDoc comment
                rmc.setMyInvGFAbs(abs.replaceAll("\\n", " "));
        }
}
