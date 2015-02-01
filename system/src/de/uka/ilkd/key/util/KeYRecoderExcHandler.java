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


public class KeYRecoderExcHandler implements recoder.service.ErrorHandler {

    private List<Throwable> exceptions = new LinkedList<Throwable>();
    private int errorThreshold;

    public void reportException(Throwable e) {
        exceptions.add(e);
        throw new ExceptionHandlerException(e);
    }


    public KeYRecoderExcHandler() {
        setErrorThreshold(0);
    }


    public KeYRecoderExcHandler(int errorThreshold) {
	 setErrorThreshold(errorThreshold);
    }


    public void clear() {
	exceptions.clear();
    }


    public List<Throwable> getExceptions() {
        List<Throwable> result = new LinkedList<Throwable>();

        if(exceptions != null)
            result.addAll(exceptions);

        return result;
    }


    // Implementation of recoder.service.ErrorHandler
    protected int getErrorCount() {
         return exceptions.size();
    }


    @Override
    public int getErrorThreshold() {
        return errorThreshold;
    }


    @Override
    public final void setErrorThreshold(int maxCount) {
        if (maxCount < 0) {
            throw new IllegalArgumentException("Recoder: Threshold should be >= 0");
        }
        errorThreshold = maxCount;
    }


    protected void recoderExitAction() {
        String msg = "Recoder: " + exceptions.size() + " errors have occurred - aborting.";
        ExceptionHandlerException ex = new ExceptionHandlerException(msg);
        if(exceptions != null && !exceptions.isEmpty()) {
            ex.initCause(exceptions.get(0));
        }
        clear();

        throw ex;
    }


    @Override
    public void reportError(Exception e) {
        exceptions.add(e);
        if (exceptions.size() > errorThreshold) {
            recoderExitAction();
        }
    }


    @Override
    public void modelUpdating(EventObject event) {
    }


    @Override
    public void modelUpdated(EventObject event) {
        if (exceptions.size() > 0) {
             recoderExitAction();
        }
    }
}