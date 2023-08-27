/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;


import java.util.EventObject;
import java.util.LinkedList;
import java.util.List;


public class KeYRecoderExcHandler implements recoder.service.ErrorHandler {

    private final List<Throwable> exceptions = new LinkedList<>();
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
        List<Throwable> result = new LinkedList<>();

        if (exceptions != null) {
            result.addAll(exceptions);
        }

        return result;
    }


    // Implementation of recoder.service.ErrorHandler
    public int getErrorCount() {
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
        if (exceptions != null && !exceptions.isEmpty()) {
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
