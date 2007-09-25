// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.ast;


import java.util.List;

import de.uka.ilkd.asmkey.util.ArrayUtil;
import de.uka.ilkd.asmkey.util.CollectionUtil;
import de.uka.ilkd.key.parser.Location;


/** This class represents a sequent (sequent calculus). It consists of
 * two lists of formulas, the antecedent and the succedent.
 *
 * @author Hubert Schmid
 */

public final class AstSequent extends AstNode {

    /** List of formulas in the antecedent. */
    private final List ant;

    /** List of formulas in the succedent. */
    private final List suc;


    public AstSequent(Location location, AstTerm[] ant, AstTerm[] suc) {
        //assert ant != null && suc != null;
        super(location);
        this.ant = ArrayUtil.toList(ant);
        this.suc = ArrayUtil.toList(suc);
    }


    /** List of formulas in the antecedent. */
    public List getAntList() {
        return ant;
    }

    /** List of formulas in the succedent. */
    public List getSucList() {
        return suc;
    }

    /** for debug only */
    public String toString() {
        return "[Sequent:ant=" + CollectionUtil.toString(ant) + ",suc=" + CollectionUtil.toString(suc) + "]";
    }

}
