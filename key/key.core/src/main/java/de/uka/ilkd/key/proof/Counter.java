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

package de.uka.ilkd.key.proof;


/** Proof-specific counter object: taclet names, var names, node numbers, &c */
public class Counter {

    private String name;
    private int count;

    public Counter(String name) {
        this.name=name;
    }
    
    private Counter(String name, int count) {
       this(name);
       this.count = count;
    }
    
    public int getCount() {
        return count;
    }
    
    public int getCountPlusPlus(){
	return count++;
    }

    /**
     * This is needed when loading e.g. persistentNodeIds from a saved proof.
     * Can only be used to increase the counter.
     * @param count new count to set. If the current count is smaller, nothing is done.
     */
    public void increaseCount(int count) {
        if (this.count < count) {
            this.count = count;
        }
    }
    
    public String toString() {
        return "Counter "+ name + ": " + count;
    }
    
    public Counter copy() {
       return new Counter(name, count);
    }
}