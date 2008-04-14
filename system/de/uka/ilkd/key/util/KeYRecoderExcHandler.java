// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;


import java.util.*;

import recoder.java.ProgramElement;
import recoder.java.reference.TypeReference;
import recoder.service.UnresolvedReferenceException;


public class KeYRecoderExcHandler extends KeYExceptionHandlerImpl implements recoder.service.ErrorHandler{

    private ExtList recoderExceptions = new ExtList();
    private int recoderErrorCount = 0;
    private int recoderErrorThreshold;
    
    private List<TypeReference> unresolvedClasses;
    
    private boolean ignoreUnresolvedClasses = false;
    
    public void reportException(Throwable e){
        super.reportException(e);
        if (getExceptions().size() != 0) {
            throw new ExceptionHandlerException(e);
        }    
    }

    public KeYRecoderExcHandler() {
           super();
	   setErrorThreshold(0);
    }
    
    public KeYRecoderExcHandler(int errorThreshold) {
         super();
	 setErrorThreshold(recoderErrorThreshold);
    }

    public void clear(){
	super.clear();
	recoderExceptions = new ExtList();
	recoderErrorCount = 0;
    }
    
    public boolean error(){
	return ((super.error()) || (!recoderExceptions.isEmpty()));
    }

    public ExtList getExceptions(){
	ExtList excList = new ExtList();
	if (!(exceptions==null))excList.addAll(exceptions);
	if (!(recoderExceptions==null))excList.addAll(recoderExceptions);
	return excList;
    }

    // Implementation of recoder.service.ErrorHandler

    protected int getErrorCount() {
         return recoderErrorCount;
    }
   
    public int getErrorThreshold() {
        return recoderErrorThreshold;
    }
    
    public void setErrorThreshold(int maxCount) {
        if (maxCount < 0) {
            throw new IllegalArgumentException("Recoder: Threshold should be >= 0");
        }
        recoderErrorThreshold = maxCount;
    }
         
 
    protected void recoderExitAction() {       
        String msg = "Recoder: " + recoderErrorCount + " errors have occured - aborting.";
	recoderErrorCount = 0;
        throw (ExceptionHandlerException) 
	    new ExceptionHandlerException(msg).initCause((Throwable)recoderExceptions.getFirst());
    }
    
    public void reportError(Exception e) {
        if(!testUnresolvedClass(e)) {
            recoderErrorCount += 1;
            recoderExceptions.add(e);
            if (recoderErrorCount > recoderErrorThreshold) {
                recoderExitAction();
            }         
        }
    }
    
    public void modelUpdating(EventObject event) {}
    
    public void modelUpdated(EventObject event) {
        if (recoderErrorCount > 0) {
             recoderExitAction();
        }
    }

    public boolean isIgnoreUnreferencedClasses() {
        return ignoreUnresolvedClasses;
    }

    /**
     * Check whether an exception is to be ignored.
     * This is the case if:
     * 1. the exception is an UnresolvedReferenceException, and
     * 2. ignoreUnresolvedClasses is set to true, and
     * 3. the unresolved reference is a type reference
     */
    private boolean testUnresolvedClass(Throwable e) {
        if (ignoreUnresolvedClasses && e instanceof UnresolvedReferenceException) {
            UnresolvedReferenceException ur = (UnresolvedReferenceException) e;
            ProgramElement ref = ur.getUnresolvedReference();
            if (ref instanceof TypeReference) {
                TypeReference tyref = (TypeReference) ref;
                unresolvedClasses.add(tyref);
                Debug.out("Unresolved type: " + ref.toSource());
                // System.err.println("Unresolved type: " + ref.toSource());
                return true;
            }
        }
        return false;
    }
    
    public void setIgnoreUnresolvedClasses(boolean ignoreUnresolvedClasses) {
        this.ignoreUnresolvedClasses = ignoreUnresolvedClasses;
        if(ignoreUnresolvedClasses)
            unresolvedClasses = new ArrayList<TypeReference>();
    }

    public List<TypeReference> getUnresolvedClasses() {
        return unresolvedClasses;
    }
    
    
}
