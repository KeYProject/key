// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.env;


import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.util.Debug;


/** Attach procedures to an instance of Services. This is an hack! In
 * some cases, the declared procedures have to be known, but there is
 * no way to pass them through. This class attaches the list of
 * procedures to an instance of Services. This instance is unique
 * during a proof session and can be accessed almost everywhere. */

public final class ProcedurePool {

    /** Return the attached list of procedures. If no procedures are
     * attached to this Services instance, an exception is thrown. The
     * elements of the collection are of type {@link
     * de.uka.ilkd.asmkey.logic.AsmProcedure}.
     */
    public static Namespace get(Services services) {
        Debug.assertTrue(map.containsKey(services));
        return (Namespace) map.get(services);
    }

    /** Attach a list of collections at an instance of Services. If
     * procedures are already attached to this object, an exception is
     * thrown. */
    public static void put(Services services, Namespace procedures) {
        Debug.assertTrue(!map.containsKey(services));
        map.put(services, procedures);
    }

    /** Stores mappings between Services and collections of
     * Procedures. */
    private static final Map map = new HashMap();

}
