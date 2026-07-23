/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.util.List;


public final class ProblemLoaderException extends Exception {

    private static final long serialVersionUID = 5683051720482052601L;
    private final AbstractProblemLoader origin;

    /**
     * Several sub-problems bundled into this single exception (e.g. all rule applications that
     * could
     * not be replayed). Empty for an ordinary single-cause exception. Lets the message extraction
     * ({@link de.uka.ilkd.key.util.ExceptionTools#getMessages}) surface every problem instead of
     * only the first.
     */
    private final List<Throwable> subExceptions;

    public ProblemLoaderException(AbstractProblemLoader origin, String msg, Throwable cause) {
        super(msg, cause);
        this.origin = origin;
        this.subExceptions = List.of();
    }

    public ProblemLoaderException(AbstractProblemLoader origin, String msg) {
        super(msg);
        this.origin = origin;
        this.subExceptions = List.of();
    }

    /**
     * Bundles several problems into one exception. The summary {@code msg} describes them; the
     * first
     * sub-exception is kept as the {@link #getCause() cause}, and the full list is available via
     * {@link #getSubExceptions()}.
     *
     * @param origin the loader that produced the problems
     * @param msg a summary message
     * @param subExceptions the individual problems (must not be empty)
     */
    public ProblemLoaderException(AbstractProblemLoader origin, String msg,
            List<Throwable> subExceptions) {
        super(msg, subExceptions.isEmpty() ? null : subExceptions.get(0));
        this.origin = origin;
        this.subExceptions = List.copyOf(subExceptions);
    }

    public AbstractProblemLoader getOrigin() {
        return origin;
    }

    /**
     * @return the bundled sub-problems, or an empty list for an ordinary single-cause exception
     */
    public List<Throwable> getSubExceptions() {
        return subExceptions;
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        if (getMessage() != null) {
            sb = sb.append(getMessage());
        }
        sb = sb.append(" (");
        if (origin == null) {
            sb = sb.append("unknown origin");
        } else {
            sb = sb.append("file: ").append(origin.getFile());
        }
        if (getCause() != null) {
            sb = sb.append("; caused by: ");
            sb = sb.append(getCause());
        }
        sb = sb.append(')');
        return sb.toString();
    }
}
