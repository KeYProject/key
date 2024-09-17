/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

public class ProblemLoaderException extends Exception {
    private final AbstractProblemLoader origin;

    public ProblemLoaderException(AbstractProblemLoader origin, Throwable cause) {
        super(cause.getMessage(), cause);
        this.origin = origin;
    }

    public ProblemLoaderException(AbstractProblemLoader origin, String msg, Throwable cause) {
        super(msg, cause);
        this.origin = origin;
    }

    public ProblemLoaderException(AbstractProblemLoader origin, String msg) {
        super(msg);
        this.origin = origin;
    }

    public AbstractProblemLoader getOrigin() {
        return origin;
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
