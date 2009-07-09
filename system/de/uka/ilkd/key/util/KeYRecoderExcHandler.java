// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;


import java.util.EventObject;


public class KeYRecoderExcHandler extends KeYExceptionHandlerImpl implements recoder.service.ErrorHandler{

    private ExtList recoderExceptions = new ExtList();
    private int recoderErrorCount = 0;
    private int recoderErrorThreshold;
    
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
	 setErrorThreshold(errorThreshold);
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
        ExceptionHandlerException ex = new ExceptionHandlerException(msg);
        ex.initCause((Throwable)recoderExceptions.getFirst());
        recoderExceptions.clear();
        
        throw ex;
    }
    
    public void reportError(Exception e) {
        recoderErrorCount += 1;
        recoderExceptions.add(e);
        if (recoderErrorCount > recoderErrorThreshold) {
            recoderExitAction();
        }         
    }
    
    public void modelUpdating(EventObject event) {}
    
    public void modelUpdated(EventObject event) {
        if (recoderErrorCount > 0) {
             recoderExitAction();
        }
    }

}
