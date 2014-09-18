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

package de.uka.ilkd.key.proof.io;


public class ProblemLoaderException
extends RuntimeException // to have it passed through the parser (without adding throws declarations everywhere)
{

    private static final long serialVersionUID = -3012196004988313969L;
    private DefaultProblemLoader origin;

    public ProblemLoaderException(DefaultProblemLoader origin, Throwable cause) {
        super(cause.getMessage(), cause);
        this.origin = origin;
    }

    public ProblemLoaderException(DefaultProblemLoader origin, String msg, Throwable cause) {
        super(msg, cause);
        this.origin = origin;
    }
    
    public ProblemLoaderException(DefaultProblemLoader origin, String msg) {
        super(msg);
        this.origin = origin;
    }

    public DefaultProblemLoader getOrigin() {
        return origin;
    }
    
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        if (getMessage() != null)
            sb = sb.append(getMessage());
        sb = sb.append(" (");
        if (origin == null) sb = sb.append("unknown origin");
        else sb = sb.append("file: ").append(origin.getFile());
        if (getCause() != null) {
            sb = sb.append("; caused by: ");
            sb = sb.append(getCause());
        }
        sb = sb.append(')');
        return sb.toString();
    }
}