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

import de.uka.ilkd.asmkey.logic.FormalParameter;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Operator;


/** TermEnvironment for parsing the body of procedures (named ASM
 * rules). The method {@link #getOperator(String)} returns the formal
 * parameter, if one with the given name exists.
 *
 * @author Hubert Schmid
 */

public final class CallEnvironment extends DelegateTermEnvironment {

    /** Return a map, that maps identifier (strings) to the
     * corresponding formal parameters. */
    private static Map getFormalParameters(FormalParameter[] params) throws EnvironmentException {
        Map map = new HashMap();
        for (int i = 0; i < params.length; ++i) {
            String id = params[i].name().toString();
            if (map.containsKey(id)) {
                throw new EnvironmentException("Formal parameter " + id + " is already defined.");
            }
            map.put(id, params[i]);
        }
        return map;
    }


    /** Stores the mappings between identifiers (strings) and formal
     * parameters. */
    private final Map map;


    /** Create a CallEnvironment that adds the formal parameters to
     * the environment. */
    public CallEnvironment(TermEnvironment env, FormalParameter[] params) throws EnvironmentException {
        super(env);
        this.map = getFormalParameters(params);
    }

    public boolean containsOperator(Name id) {
	if (map.containsKey(id.toString())) {
	    return true;
	} else {
	    return super.containsOperator(id);
	}
    }

    /** If a formal parameter with the given name exists, this method
     * returns this paramter. Else the method forwards the query to
     * the default TermEnvironment. */
    public Operator getOperator(Name id) throws EnvironmentException {

        if (map.containsKey(id.toString())) {
            return (Operator) map.get(id.toString());
        } else {
            return super.getOperator(id);
        }
    }

    public boolean isParsingDerivedFunction() {
	return true;
    }

}
