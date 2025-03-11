/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.EventObject;

import recoder.ModelElement;
import recoder.ModelException;
import recoder.java.ProgramElement;

public class DefaultErrorHandler implements ErrorHandler {

    private int errorCount = 0;

    private int errorThreshold;

    public DefaultErrorHandler() {
        setErrorThreshold(20);
    }

    public DefaultErrorHandler(int errorThreshold) {
        setErrorThreshold(errorThreshold);
    }

    /**
     * Returns the current error count.
     */
    protected int getErrorCount() {
        return errorCount;
    }

    public int getErrorThreshold() {
        return errorThreshold;
    }

    public void setErrorThreshold(int maxCount) {
        if (maxCount < 0) {
            throw new IllegalArgumentException("Threshold should be >= 0");
        }
        errorThreshold = maxCount;
    }

    /**
     * Redefine this method to indicate that the specified element refers to unavailable code. This
     * suppresses corresponding unresolved reference errors. The default implementation returns
     * <CODE>false</CODE>.
     */
    protected boolean isReferingUnavailableCode(@SuppressWarnings("unused") ModelElement me) {
        return false;
    }

    /**
     * Redefine this method to indicate that the specified element belongs to a code template. This
     * suppresses corresponding unresolved reference errors. The default implementation returns
     * <CODE>false</CODE>.
     */
    protected boolean isTemplateCode(@SuppressWarnings("unused") ProgramElement pe) {
        return false;
    }

    /**
     * Redefine this method to filter exceptions that are not considered as an error. The default
     * implementation checks for {@link recoder.service.UnresolvedReferenceException}s and returns
     * <CODE>
     * true</CODE> if the cause is either part of an incomplete model or contained in template code.
     *
     * @see #isReferingUnavailableCode
     * @see #isTemplateCode
     */
    protected boolean isIgnorable(Exception e) {
        if (e instanceof UnresolvedReferenceException) {
            ProgramElement unresolvedReference =
                ((UnresolvedReferenceException) e).getUnresolvedReference();
            if (isReferingUnavailableCode(unresolvedReference)) {
                return true;
            }
            return isTemplateCode(unresolvedReference);
        }
        return false;
    }

    /**
     * Issues a warning message when the specified exception is ignored. The default implementation
     * writes a note to stderr.
     */
    protected void warningMessage(Exception e) {
        String className = e.getClass().getName();
        className = className.substring(className.lastIndexOf('.') + 1);
        System.err.println("+++ Warning: " + className);
        System.err.println(e.getMessage());
        System.err.println();
    }

    /**
     * Issues an error message when the specified exception is not ignored, but the system will
     * continue to find further errors. The default implementation writes a note to stderr.
     */
    protected void errorMessage(Exception e) {
        String className = e.getClass().getName();
        className = className.substring(className.lastIndexOf('.') + 1);
        System.err.println("*** " + errorCount + ": " + className);
        System.err.println(e.getMessage());
        System.err.println();
    }

    /**
     * Called when too many errors occurred or the model update has finished and there were
     * non-ignorable errors. The default implementation writes a message to stderr and throws a
     * model exception.
     */
    protected void exitAction() {
        String msg = "" + errorCount + " errors have occured - aborting.";
        System.err.println(msg);
        throw new ModelException(msg);
    }

    public void reportError(Exception e) {
        if (isIgnorable(e)) {
            warningMessage(e);
        } else {
            errorCount += 1;
            errorMessage(e);
            if (errorCount > errorThreshold) {
                exitAction();
            }
        }
    }

    public void modelUpdating(@SuppressWarnings("unused") EventObject event) {
        // ignore
    }

    public void modelUpdated(@SuppressWarnings("unused") EventObject event) {
        if (errorCount > 0) {
            exitAction();
        }
    }
}
