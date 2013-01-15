// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class Person {
    private int age = 0;

    public void setAge(int newAge) {
	this.age = newAge;
    }

    public void birthday() {
	if (age >= 0) {
	    age++;
	} 
    }
}
