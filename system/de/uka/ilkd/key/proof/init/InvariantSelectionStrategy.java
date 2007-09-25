//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;


/** 
 * Describes which invariants are to be preselected (i.e. assumed by default), 
 * and for which ones an insertion rule is created which allows the user to 
 * select them when needed.
 */
public abstract class InvariantSelectionStrategy {

    /**
     * A strategy which preselects all invariants.
     */
    public final static InvariantSelectionStrategy PRESELECT_ALL 
            = new InvariantSelectionStrategy() {
        public boolean preselectAll() {
            return true;
        }
        public boolean preselectPackage() {
            return true;
        }
        public boolean preselectClass() {
            return true;
        }
    };
    
    
    /**
     * A strategy which preselects the invariants of the own package only.
     */
    public final static InvariantSelectionStrategy PRESELECT_PACKAGE
            = new InvariantSelectionStrategy() {
        public boolean preselectAll() {
            return false;
        }
        public boolean preselectPackage() {
            return true;
        }
        public boolean preselectClass() {
            return true;
        }
    };
    
    
    /**
     * A strategy which preselects the invariants of the own class only.
     */
    public final static InvariantSelectionStrategy PRESELECT_CLASS 
            = new InvariantSelectionStrategy() {
        public boolean preselectAll() {
            return false;
        }
        public boolean preselectPackage() {
            return false;
        }
        public boolean preselectClass() {
            return true;
        }
    };
    
    
    /**
     * A strategy which preselects no invariants at all.
     */
    public final static InvariantSelectionStrategy PRESELECT_NONE 
            = new InvariantSelectionStrategy() {
        public boolean preselectAll() {
            return false;
        }
        public boolean preselectPackage() {
            return false;
        }
        public boolean preselectClass() {
            return false;
        }
    };   
    
    
    public abstract boolean preselectAll();
    
    
    public abstract boolean preselectPackage();
    
    
    public abstract boolean preselectClass();
}
