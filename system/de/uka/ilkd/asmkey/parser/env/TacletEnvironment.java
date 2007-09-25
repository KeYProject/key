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


import java.util.*;

import de.uka.ilkd.key.rule.Taclet;


/** DeclarationEnvironment for parsing <b>local</b> taclets. The
 * declared taclets are added to a local list and not to the the
 * default DeclarationEnvironment.
 *
 * @author Hubert Schmid
 */

public final class TacletEnvironment extends DelegateDeclarationEnvironment {

    /** This map stores the local (new) declared taclets. */
    private final Map taclets = new HashMap();


    public TacletEnvironment(DeclarationEnvironment env) {
        super(env);
    }


    public void addTaclet(Taclet t) throws EnvironmentException {
        String id = t.name().toString();
        if (taclets.containsKey(id)) {
            throw new EnvironmentException("Taclet " + id + " is already defined.");
        } else {
            taclets.put(id, t);
        }
    }

    /** Returns all local declared taclets. */
    public Collection getLocalTaclets() {
        return Collections.unmodifiableCollection(new ArrayList(taclets.values()));
    }

}
