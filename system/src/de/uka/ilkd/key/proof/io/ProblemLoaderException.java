// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
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


    private static final long serialVersionUID = -8442899290593478727L;
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
}