// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.asmkey.logic.dfinfo.DFInfo;

/** Interface for accessing the AccessDFInfo of AsmTerm, which is
 * a package private class.
 *
 * @author Stanislas Nanchen
 */
public interface AccessDFInfoContainer {

    public DFInfo getAccessDFInfo();

    public void setAccessDFInfo(DFInfo info);

}
