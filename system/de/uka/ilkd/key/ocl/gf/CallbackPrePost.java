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

import de.uka.ilkd.key.casetool.ModelMethod;

/** 
 * the GF editor uses this class as an interface for sending 
 * pre-/postconditions to Together
 * @author Kristofer Johannisson & Hans-Joachim Daniels 
 */
public class CallbackPrePost extends ConstraintCallback {
        
        private ModelMethod rmm; 
        
        /**
         * just sets the field rmm
         * @param rmm A representation of the method in the model,
         * used to create the initial stub for GF and to save the constraint there.
         */
        public CallbackPrePost(ModelMethod rmm) {
                this.rmm = rmm;
        }
        
        /**
         * saves the given OCL constraint in the Java file as a JavaDoc comment.
         * @param ocl assumption: ocl constraint has form ... .. pre: .... ... post: ...
         * Only one pre- and one postcondition is supported by TogetherCC! 
         */
        public void sendConstraint(String ocl) {
                if (logger.isLoggable(Level.FINE)) {
                        logger.fine("sendPrePost received OCL: " + ocl);
                }

                final int postEnd = ocl.length();
                final int postStart = ocl.lastIndexOf("post:") + 5;
                final int preEnd = postStart - 5;
                final int preStart = ocl.lastIndexOf("pre:", preEnd) + 4;
                final String preCond = ocl.substring(preStart, preEnd).trim();
                final String postCond = ocl.substring(postStart, postEnd).trim();
                if (logger.isLoggable(Level.FINE)) {
                        logger.fine("pre:  " + preCond);
                        logger.fine("post: " + postCond);
                }
                
                //rmm.setMyGFAbs(abs);
                rmm.setMyPreCond(preCond);
                rmm.setMyPostCond(postCond);
                rmm.setMyGFAbs(null); //delete that JavaDoc comment
        }
        
        /**
         * saves the given OCL constraint in the Java file as a JavaDoc comment
         * in the GF tree syntax
         * @param abs GF abstract syntax tree 
         */
        public void sendAbstract(String abs) {
                if (logger.isLoggable(Level.FINE)) {
                        logger.fine("sendPrePost received AST: " + abs);
                }
                //pass AST to Together
                rmm.setMyGFAbs(abs.replaceAll("\\n", " "));
                rmm.setMyPreCond(null); //delete that JavaDoc comment
                rmm.setMyPostCond(null); //delete that JavaDoc comment
        }
}
