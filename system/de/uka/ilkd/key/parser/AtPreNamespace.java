// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.parser;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Used by the parser to create @pre-functions on demand.
 */
public class AtPreNamespace extends Namespace {

    private final Map atPreMapping;
    private final JavaInfo javaInfo;
    
    public AtPreNamespace(Namespace parent, JavaInfo ji) {
        super(parent);
        this.javaInfo = ji;
        this.atPreMapping = new HashMap();
    }
    
    public Named lookup(Name name) {
        Named n = super.lookup(name);
        if (n==null && name.toString().endsWith("@pre")) {
            Name atPostName = new Name(name.toString().substring
                                  (0, name.toString().length()-4));
            Named atPost = (Named) super.lookup(atPostName);
            if (atPost==null) {
                if (atPostName.toString().indexOf("::")>=0) {
                    atPost = javaInfo.getAttribute(atPostName.toString());
                }
                if (atPost==null) {
                    return null;
                }
            }
                  
            n = (Named) atPreMapping.get(atPost);
            if (n==null) {
                if (atPost instanceof ProgramVariable) {
                    ProgramVariable pv = (ProgramVariable) atPost;
                    final Sort[] argSorts;
                    if (pv.isMember() && !pv.isStatic()) {
                        argSorts = new Sort[]{ pv.getContainerType().getSort()};
                        if (argSorts[0] == null) { // in the case of array length
                            argSorts[0] = javaInfo.getJavaLangObjectAsSort();
                        }                        
                    } else {
                        argSorts = new Sort[0];
                    }
                    n = createAtPreFunction(name, pv.sort(), new ArrayOfSort(argSorts));
                } else if (atPost instanceof Function) {
                    n = createAtPreFunction(name, ((Function)atPost).sort(), ((Function)atPost).argSort());
                } 
                atPreMapping.put(atPost, n);
            }
        }
        return n;
    }

    /**
     */
    private Named createAtPreFunction(Name name, Sort sort, ArrayOfSort argsort) {
        return new RigidFunction(name, sort, argsort);
    }

    public Map getAtPreMapping() {
        return atPreMapping;
    }

}
