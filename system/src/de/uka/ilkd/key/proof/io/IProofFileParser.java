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

import java.util.List;

/**
 * Defines the required which a {@link KeYParser} needs to parse a *.proof
 * file and to apply the reules again.
 * @author Martin Hentschel
 */
public interface IProofFileParser {
   void beginExpr(char eid, String str);

   void endExpr(char eid, int stringLiteralLine);

   String getStatus();

   List<Throwable> getErrors();
}