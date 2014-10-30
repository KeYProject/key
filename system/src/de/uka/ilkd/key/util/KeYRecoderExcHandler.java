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

package de.uka.ilkd.key.util;


import java.util.*;


public class KeYRecoderExcHandler extends AbstractKeYExceptionHandler 
                                  implements recoder.service.ErrorHandler {

    private List<Throwable> recoderExceptions = new LinkedList<Throwable>();
    private int recoderErrorCount = 0;
    private int recoderErrorThreshold;
    
    
    @Override
    public void reportException(Throwable e) {
        super.reportException(e);
        if(!getExceptions().isEmpty()) {
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
    

    @Override    
    public void clear() {
	super.clear();
	recoderExceptions = new LinkedList<Throwable>();
	recoderErrorCount = 0;
    }
    

    @Override    
    public List<Throwable> getExceptions() {
        List<Throwable> result = new LinkedList<Throwable>();
        
        if(exceptions != null)
            result.addAll(exceptions);
        
        if(recoderExceptions != null)
            result.addAll(recoderExceptions);
        
	return result;
    }

    
    // Implementation of recoder.service.ErrorHandler

    protected int getErrorCount() {
         return recoderErrorCount;
    }
   
    
    @Override
    public int getErrorThreshold() {
        return recoderErrorThreshold;
    }
    
    
    @Override    
    public final void setErrorThreshold(int maxCount) {
        if (maxCount < 0) {
            throw new IllegalArgumentException("Recoder: Threshold should be >= 0");
        }
        recoderErrorThreshold = maxCount;
    }
         
 
    protected void recoderExitAction() {       
        String msg = "Recoder: " + recoderErrorCount + " errors have occurred - aborting.";
	recoderErrorCount = 0;
        ExceptionHandlerException ex = new ExceptionHandlerException(msg);
        ex.initCause(recoderExceptions.get(0));
        recoderExceptions.clear();
        
        throw ex;
    }
    
    
    @Override    
    public void reportError(Exception e) {
        recoderErrorCount += 1;
        recoderExceptions.add(e);
        if (recoderErrorCount > recoderErrorThreshold) {
            recoderExitAction();
        }         
    }
    
    
    @Override    
    public void modelUpdating(EventObject event) {
    }
    
    
    @Override    
    public void modelUpdated(EventObject event) {
        if (recoderErrorCount > 0) {
             recoderExitAction();
        }
    }
}